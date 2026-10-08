-- Prove2me | solution 1 for DGPNash.WellSupported.trim_is_well_supported
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:32:21.10444+00:00
-- url     : https://prove2.me/submissions/2cdbc751-5e1f-4331-9b7d-8dc8c75dd71d

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria



namespace DGPNash.WellSupported

open Finset

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

lemma ws_prod_update (z : ∀ i, S i → ℝ) (i : ι) (c : S i → ℝ)
    (s : ∀ i, S i) :
    ∏ k, (Function.update z i c) k (s k) = c (s i) * ∏ k ∈ univ.erase i, z k (s k) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

lemma ws_sum_prod (w : ∀ i, S i → ℝ) :
    ∑ s : (∀ i, S i), ∏ k, w k (s k) = ∏ k, ∑ j, w k j := by
  rw [Fintype.prod_sum]

lemma ws_lemA (u : ι → (∀ i, S i) → ℝ) (p : ι) (M : ℝ)
    (hu0 : ∀ s, 0 ≤ u p s) (huM : ∀ s, u p s ≤ M)
    (z : ∀ i, S i → ℝ) (hz : AGT.IsMixedProfile z) (i : ι) (a b : S i → ℝ) :
    |AGT.expectedPayoff u (Function.update z i a) p - AGT.expectedPayoff u (Function.update z i b) p|
      ≤ M * ∑ j, |a j - b j| := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [← Finset.sum_sub_distrib]
  have key : ∀ s : (∀ i, S i),
      |(∏ k, (Function.update z i a) k (s k)) * u p s - (∏ k, (Function.update z i b) k (s k)) * u p s|
        ≤ M * ∏ k, (Function.update z i (fun j => |a j - b j|)) k (s k) := by
    intro s
    rw [ws_prod_update, ws_prod_update, ws_prod_update]
    have hQ : 0 ≤ ∏ k ∈ univ.erase i, z k (s k) := Finset.prod_nonneg (fun k _ => (hz k).1 _)
    rw [show a (s i) * (∏ k ∈ univ.erase i, z k (s k)) * u p s
        - b (s i) * (∏ k ∈ univ.erase i, z k (s k)) * u p s
        = (a (s i) - b (s i)) * ((∏ k ∈ univ.erase i, z k (s k)) * u p s) by ring]
    rw [abs_mul, abs_of_nonneg (mul_nonneg hQ (hu0 s))]
    have := hu0 s; have := huM s
    have h1 : 0 ≤ |a (s i) - b (s i)| := abs_nonneg _
    calc |a (s i) - b (s i)| * ((∏ k ∈ univ.erase i, z k (s k)) * u p s)
        ≤ |a (s i) - b (s i)| * ((∏ k ∈ univ.erase i, z k (s k)) * M) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ s : (∀ i, S i), |(∏ k, (Function.update z i a) k (s k)) * u p s - (∏ k, (Function.update z i b) k (s k)) * u p s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : (∀ i, S i), M * ∏ k, (Function.update z i (fun j => |a j - b j|)) k (s k) :=
        Finset.sum_le_sum (fun s _ => key s)
    _ = M * ∑ j, |a j - b j| := by
        rw [← Finset.mul_sum, ws_sum_prod]
        congr 1
        rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
        simp only [Function.update_self]
        rw [Finset.prod_eq_one, mul_one]
        intro k hk
        rw [Function.update_of_ne (ne_of_mem_erase hk)]
        exact (hz k).2

lemma ws_lemB (u : ι → (∀ i, S i) → ℝ) (p : ι) (M : ℝ)
    (hu0 : ∀ s, 0 ≤ u p s) (huM : ∀ s, u p s ≤ M)
    (x x' : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x') :
    |AGT.expectedPayoff u x p - AGT.expectedPayoff u x' p|
      ≤ M * ∑ i, ∑ j, |x i j - x' i j| := by
  let h : Finset ι → ∀ i, S i → ℝ := fun T k => if k ∈ T then x' k else x k
  have hmix : ∀ T, AGT.IsMixedProfile (h T) := by
    intro T k; by_cases hk : k ∈ T <;> simp [h, hk, hx k, hx' k]
  have claim : ∀ T : Finset ι, |AGT.expectedPayoff u x p - AGT.expectedPayoff u (h T) p|
      ≤ M * ∑ i ∈ T, ∑ j, |x i j - x' i j| := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : h ∅ = x := by funext k; simp [h]
      simp [this]
    | insert a T ha ih =>
      have e1 : h (insert a T) = Function.update (h T) a (x' a) := by
        funext k; by_cases hk : k = a
        · subst hk; simp [h]
        · simp [h, hk, Function.update_of_ne hk]
      have e2 : h T = Function.update (h T) a (x a) := by
        funext k; by_cases hk : k = a
        · subst hk; simp [h, ha]
        · simp [Function.update_of_ne hk]
      have := ws_lemA u p M hu0 huM (h T) (hmix T) a (x a) (x' a)
      rw [← e2, ← e1] at this
      rw [Finset.sum_insert ha, mul_add]
      calc _ ≤ |AGT.expectedPayoff u x p - AGT.expectedPayoff u (h T) p|
            + |AGT.expectedPayoff u (h T) p - AGT.expectedPayoff u (h (insert a T)) p| :=
              abs_sub_le _ _ _
        _ ≤ _ := by linarith
  have hu : h univ = x' := by funext k; simp [h]
  simpa [hu] using claim univ

lemma ws_linear (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ)
    (p : ι) (y : S p → ℝ) :
    AGT.expectedPayoff u (Function.update x p y) p = ∑ j, y j * DGPNash.NashMap.purePayoff u x p j := by
  unfold DGPNash.NashMap.purePayoff AGT.expectedPayoff AGT.profileProb
  simp_rw [ws_prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 2
  simp [mul_ite]

lemma ws_pure_mixed (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (p : ι)
    (j : S p) : AGT.IsMixedProfile (Function.update x p (fun k => if k = j then 1 else 0)) := by
  intro i
  by_cases hi : i = p
  · subst hi; simp only [Function.update_self]
    refine ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
  · rw [Function.update_of_ne hi]; exact hx i

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

lemma ws_U_le (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) (j : S p) :
    DGPNash.NashMap.purePayoff u x p j ≤ maxPurePayoff u x p :=
  le_ciSup (f := fun j => DGPNash.NashMap.purePayoff u x p j) (Set.finite_range _).bddAbove j

lemma ws_key (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε)
    (p : ι) :
    ∑ j, x p j * (maxPurePayoff u x p - DGPNash.NashMap.purePayoff u x p j) ≤ ε := by
  have hne : Nonempty (S p) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (hx.1 p).2
    simp at this
  obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := fun j => DGPNash.NashMap.purePayoff u x p j)
  have hdev := hx.2 p (fun k => if k = j0 then 1 else 0)
    ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
  have hE : AGT.expectedPayoff u x p = ∑ j, x p j * DGPNash.NashMap.purePayoff u x p j := by
    rw [← ws_linear u x p (x p), Function.update_eq_self]
  have hmax : maxPurePayoff u x p = DGPNash.NashMap.purePayoff u x p j0 := hj0.symm
  have h1 : AGT.expectedPayoff u (Function.update x p (fun k => if k = j0 then 1 else 0)) p
      = maxPurePayoff u x p := by rw [hmax]; rfl
  rw [h1, hE] at hdev
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hx.1 p).2, one_mul]
  linarith

theorem claim5_core (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 0 < k) (p : ι) :
    trimMass u x ε k p ≤ 1 / k := by
  have key := ws_key u x ε hx p
  have hU := ws_U_le u x p
  have hx0 := (hx.1 p).1
  have hterm : ∀ j, 0 ≤ x p j * (maxPurePayoff u x p - DGPNash.NashMap.purePayoff u x p j) :=
    fun j => mul_nonneg (hx0 j) (by linarith [hU j])
  have hsum0 := Finset.sum_nonneg (fun j (_ : j ∈ univ) => hterm j)
  rcases lt_trichotomy ε 0 with hε | hε | hε
  · linarith
  · subst hε
    have hz : trimMass u x 0 k p = 0 := by
      unfold trimMass
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with h
      · have h0 : ∑ j, x p j * (maxPurePayoff u x p - DGPNash.NashMap.purePayoff u x p j) = 0 :=
          le_antisymm key hsum0
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)] at h0
        have := h0 j (mem_univ _)
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · simp at h; linarith
      · rfl
    rw [hz]; positivity
  · have : ε * k * trimMass u x ε k p ≤ ε := by
      refine le_trans ?_ key
      unfold trimMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · have := hx0 j
        nlinarith
      · simpa using hterm j
    rw [le_div_iff₀ hk]
    nlinarith

lemma ws_trimMass_nonneg (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (p : ι) : 0 ≤ trimMass u x ε k p := by
  unfold trimMass
  exact Finset.sum_nonneg (fun j _ => by split_ifs; exact (hx p).1 j; rfl)

lemma ws_trim_eq (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) (p : ι) (j : S p) :
    trim u x ε k p j = (x p j - (if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k
      then x p j else 0)) / (1 - trimMass u x ε k p) := by
  unfold trim
  by_cases h : DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k
  · rw [if_neg (not_le.mpr h), if_pos h]; simp
  · rw [if_pos (le_of_not_gt h), if_neg h, sub_zero]

theorem claim6_core (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 1 < k) (p : ι) :
    ∑ j : S p, |x p j - trim u x ε k p j| ≤ 2 / (k - 1) := by
  have hz1 := claim5_core u x ε hx k (by linarith) p
  have hz0 := ws_trimMass_nonneg u x hx.1 ε k p
  set z := trimMass u x ε k p with hzdef
  have hzlt : z < 1 := lt_of_le_of_lt hz1 (by rw [div_lt_one (by linarith)]; exact hk)
  have hpos : 0 < 1 - z := by linarith
  have hpt : ∀ j, |x p j - trim u x ε k p j| =
      (if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k then x p j else 0)
      + (x p j - (if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k
          then x p j else 0)) * (z / (1 - z)) := by
    intro j
    rw [ws_trim_eq, ← hzdef]
    have hxj := (hx.1 p).1 j
    split_ifs with h
    · simp [abs_of_nonneg hxj]
    · rw [sub_zero, zero_add]
      have e : x p j - x p j / (1 - z) = -(x p j * (z / (1 - z))) := by
        field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (mul_nonneg hxj (div_nonneg hz0 hpos.le))]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, (hx.1 p).2]
  have hz' : ∑ j, (if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k
      then x p j else 0) = z := rfl
  rw [hz', mul_div_cancel₀ _ hpos.ne']
  calc z + z ≤ 2 / k := by rw [le_div_iff₀ (by linarith)] at hz1 ⊢; linarith
    _ ≤ 2 / (k - 1) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma ws_maxPayoff_ge (u : ι → (∀ i, S i) → ℝ) (p : ι) (s : ∀ i, S i) :
    u p s ≤ maxPayoff u :=
  le_trans (le_ciSup (f := fun s => u p s) (Set.finite_range _).bddAbove s)
    (le_ciSup (f := fun p => ⨆ s, u p s) (Set.finite_range _).bddAbove p)

lemma ws_trim_mixed (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (k : ℝ) (hk : 1 < k) :
    AGT.IsMixedProfile (trim u x ε k) := by
  intro p
  have hz1 := claim5_core u x ε hx k (by linarith) p
  have hz0 := ws_trimMass_nonneg u x hx.1 ε k p
  have hzlt : trimMass u x ε k p < 1 :=
    lt_of_le_of_lt hz1 (by rw [div_lt_one (by linarith)]; exact hk)
  have hpos : 0 < 1 - trimMass u x ε k p := by linarith
  refine ⟨fun j => ?_, ?_⟩
  · rw [ws_trim_eq]
    apply div_nonneg _ hpos.le
    have := (hx.1 p).1 j
    split_ifs <;> linarith
  · simp_rw [ws_trim_eq]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, (hx.1 p).2]
    exact div_self hpos.ne'

theorem trim_core (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hε : 0 < ε) (hx : IsEpsApproxNash u x ε) :
    IsEpsWellSupportedNash u (trim u x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 1 + 4 * ((Fintype.card ι : ℝ) - 1) * maxPayoff u)) := by
  set s := Real.sqrt ε with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hε
  have hss : s * s = ε := Real.mul_self_sqrt hε.le
  set k := 1 + 1 / s with hkdef
  have hk : 1 < k := by rw [hkdef]; have := one_div_pos.mpr hs0; linarith
  have hk1 : 2 / (k - 1) = 2 * s := by
    rw [hkdef]; field_simp; ring
  have hεk : ε * k = s * s + s := by
    rw [hkdef, ← hss]; field_simp
  set M := maxPayoff u with hM
  have hmix := ws_trim_mixed u x ε hx k hk
  refine ⟨hmix, ?_⟩
  intro p j j' hgt
  by_contra hne
  have hkept : DGPNash.NashMap.purePayoff u x p j' ≥ maxPurePayoff u x p - ε * k := by
    by_contra h
    apply hne
    unfold trim
    rw [if_neg h]
  have hUj := ws_U_le u x p j
  -- payoff perturbation bound
  have hpert : ∀ l : S p, |DGPNash.NashMap.purePayoff u x p l
      - DGPNash.NashMap.purePayoff u (trim u x ε k) p l| ≤ M * (((Fintype.card ι : ℝ) - 1) * (2 * s)) := by
    intro l
    unfold DGPNash.NashMap.purePayoff
    refine le_trans (ws_lemB u p M (hu p) (ws_maxPayoff_ge u p) _ _
      (ws_pure_mixed x hx.1 p l) (ws_pure_mixed _ hmix p l)) ?_
    have hM0 : 0 ≤ M := by
      have hne : ∀ i, Nonempty (S i) := by
        intro i
        by_contra h
        rw [not_nonempty_iff] at h
        have := (hx.1 i).2
        simp at this
      exact le_trans (hu p (fun i => Classical.choice (hne i))) (ws_maxPayoff_ge u p _)
    apply mul_le_mul_of_nonneg_left _ hM0
    rw [← Finset.add_sum_erase _ _ (mem_univ p)]
    have h0 : ∑ j, |Function.update x p (fun k => if k = l then (1:ℝ) else 0) p j
        - Function.update (trim u x ε k) p (fun k => if k = l then (1:ℝ) else 0) p j| = 0 := by
      simp
    rw [h0, zero_add]
    have hb : ∀ i ∈ univ.erase p, ∑ j, |Function.update x p (fun k => if k = l then (1:ℝ) else 0) i j
        - Function.update (trim u x ε k) p (fun k => if k = l then (1:ℝ) else 0) i j| ≤ 2 * s := by
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_erase hi), Function.update_of_ne (ne_of_mem_erase hi),
        ← hk1]
      exact claim6_core u x ε hx k hk i
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hb) (le_of_eq ?_)
    rw [Finset.card_erase_of_mem (mem_univ p), Finset.card_univ, nsmul_eq_mul,
      Nat.cast_sub (by omega)]
    simp
  have h1 := abs_le.mp (hpert j)
  have h2 := abs_le.mp (hpert j')
  have : DGPNash.NashMap.purePayoff u (trim u x ε k) p j
      - DGPNash.NashMap.purePayoff u (trim u x ε k) p j'
      ≤ s * (s + 1 + 4 * ((Fintype.card ι : ℝ) - 1) * M) := by
    nlinarith
  linarith

end
end DGPNash.WellSupported

open DGPNash.WellSupported


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hε : 0 < ε) (hx : IsEpsApproxNash u x ε) :
    IsEpsWellSupportedNash u (trim u x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 1 + 4 * ((Fintype.card ι : ℝ) - 1) * maxPayoff u)) := by
  exact trim_core u hu hr x ε hε hx
