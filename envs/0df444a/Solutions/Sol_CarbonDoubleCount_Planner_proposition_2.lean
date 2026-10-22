-- Prove2me | solution 1 for CarbonDoubleCount.Planner.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:26:17.275841+00:00
-- url     : https://prove2.me/submissions/2710fdb2-1a28-4ca1-ada9-d6eb322b7132

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

set_option autoImplicit false

namespace P2Aux

open CarbonDoubleCount.Planner

/-- Chain rule: the derivative of `H ∘ Φ` is the sum of partial derivatives `dFoot`. -/
theorem hasDerivAt_comp_foot {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : (κ → ℝ) → ℝ) (hH : Differentiable ℝ H) (Φ : ℝ → κ → ℝ) (Φ' : κ → ℝ) (t0 : ℝ)
    (hΦ : HasDerivAt Φ Φ' t0) :
    HasDerivAt (fun t => H (Φ t)) (∑ i, dFoot H (Φ t0) i * Φ' i) t0 := by
  have h1 : HasDerivAt (fun t => H (Φ t)) (fderiv ℝ H (Φ t0) Φ') t0 :=
    (hH (Φ t0)).hasFDerivAt.comp_hasDerivAt t0 hΦ
  refine h1.congr_deriv ?_
  symm
  have hsingle : ∀ i, dFoot H (Φ t0) i = fderiv ℝ H (Φ t0) (Pi.single i 1) := by
    intro i
    unfold dFoot
    have h2 := (hH (Function.update (Φ t0) i (Φ t0 i))).hasFDerivAt.comp_hasDerivAt (Φ t0 i)
      (hasDerivAt_update (Φ t0) i (Φ t0 i))
    rw [Function.update_eq_self] at h2
    exact h2.deriv
  simp only [hsingle]
  conv_rhs => rw [← Finset.univ_sum_single Φ']
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (Pi.single i (Φ' i) : κ → ℝ) = Φ' i • (Pi.single i 1 : κ → ℝ) by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]]
  rw [map_smul, smul_eq_mul, mul_comm]

/-- A function antitone on `[0,A]` has nonpositive derivative at an interior point. -/
theorem deriv_nonpos_of_antitoneOn_Icc {g : ℝ → ℝ} {A t0 : ℝ}
    (hg : AntitoneOn g (Set.Icc 0 A)) (ht : t0 ∈ Set.Ioo 0 A) : deriv g t0 ≤ 0 := by
  have hA : 0 ≤ A := ht.1.le.trans ht.2.le
  set c : ℝ → ℝ := fun t => max 0 (min A t) with hcdef
  have hc : ∀ t, c t ∈ Set.Icc 0 A := fun t => ⟨le_max_left _ _, max_le hA (min_le_left _ _)⟩
  have hmono : Monotone c := fun a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
  have hanti : Antitone (g ∘ c) := fun a b hab => hg (hc a) (hc b) (hmono hab)
  have heq : (g ∘ c) =ᶠ[nhds t0] g := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t htt
    simp [c, min_eq_right htt.2.le, max_eq_right htt.1.le]
  rw [← heq.deriv_eq]
  exact hanti.deriv_nonpos

end P2Aux

open CarbonDoubleCount.Planner in
theorem solution {ι : Type} {act : ι → Type} {κ : Type}
    [Fintype ι] [DecidableEq ι]
    [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    [Fintype κ] [DecidableEq κ]
    (A pS : ℝ) (hA : 0 < A) (hpS : 0 < pS)
    (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (effortBox A))
    (hfnonneg : ∀ e ∈ effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ)
    (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ effortBox A, ∀ n i,
      (B n i = 1 ↔ (∑ j, dEff (fun e => f e i) e n j) < 0))
    (estar : (n : ι) → act n → ℝ)
    (hfb : IsFirstBest A V f pS estar)
    (hint : ∀ n j, 0 < estar n j ∧ estar n j < A)
    (huniq : ∀ e ∈ effortBox A, IsFirstBest A V f pS e → e = estar)
    (hjoint : JointProduction B)
    (fhat g h : ι → (κ → ℝ) → ℝ)
    (h5 : ∀ n φ, (∀ i, 0 ≤ φ i) → h n φ = pS * fhat n φ + g n φ)
    (hg : ∀ φ : κ → ℝ, (∀ i, 0 ≤ φ i) → ∑ n, g n φ = 0)
    (hdiff : ∀ n, Differentiable ℝ (h n))
    (hmono : ∀ n, Monotone (h n))
    (hnash : IsNash A V f h estar) :
    DoubleCounts h pS (f estar) := by
  -- the curve moving firm `n`'s action `j`
  let u : (n : ι) → act n → ℝ → ((m : ι) → act m → ℝ) :=
    fun n j t => Function.update estar n (Function.update (estar n) j t)
  have hu_diff : ∀ n j t, DifferentiableAt ℝ (u n j) t := by
    intro n j t
    exact (hasFDerivAt_update estar (Function.update (estar n) j t)).differentiableAt.comp t
      (hasDerivAt_update (estar n) j t).differentiableAt
  have hu0 : ∀ n j, u n j (estar n j) = estar := by
    intro n j
    simp [u]
  have hbox := hfb.1
  have hu_box : ∀ n j t, t ∈ Set.Icc 0 A → u n j t ∈ effortBox A := by
    intro n j t ht m k
    rcases eq_or_ne m n with rfl | hm
    · rcases eq_or_ne k j with rfl | hk
      · simpa [u] using ht
      · simpa [u, Function.update_of_ne hk] using hbox m k
    · simpa [u, Function.update_of_ne hm] using hbox m k
  have hu_mono : ∀ n j, Monotone (u n j) := by
    intro n j a b hab m k
    rcases eq_or_ne m n with rfl | hm
    · rcases eq_or_ne k j with rfl | hk
      · simpa [u] using hab
      · simp [u, Function.update_of_ne hk]
    · simp [u, Function.update_of_ne hm]
  have hmemIoo : ∀ n j, estar n j ∈ Set.Ioo 0 A := fun n j => ⟨(hint n j).1, (hint n j).2⟩
  -- marginal charges
  set H : ι → κ → ℝ := fun n i => dFoot (h n) (f estar) i with hHdef
  have hH0 : ∀ n i, 0 ≤ H n i := by
    intro n i
    apply Monotone.deriv_nonneg
    intro a b hab
    apply hmono n
    intro k
    rcases eq_or_ne k i with rfl | hk
    · simpa using hab
    · simp [Function.update_of_ne hk]
  -- sign of the effort derivatives
  have hd : ∀ n j i, dEff (fun e => f e i) estar n j ≤ 0 := by
    intro n j i
    unfold dEff
    apply P2Aux.deriv_nonpos_of_antitoneOn_Icc (A := A) _ (hmemIoo n j)
    intro a ha b hb hab
    exact hfanti i (hu_box n j a ha) (hu_box n j b hb) (hu_mono n j hab)
  -- the two first-order conditions combine to one identity per (n, j)
  have key : ∀ n j, ∑ i, (pS - H n i) * dEff (fun e => f e i) estar n j = 0 := by
    intro n j
    set t0 := estar n j with ht0
    have hV : HasDerivAt (fun t => V n (Function.update (estar n) j t))
        (deriv (fun t => V n (Function.update (estar n) j t)) t0) t0 :=
      ((hVdiff n).differentiableAt.comp t0
        (hasDerivAt_update (estar n) j t0).differentiableAt).hasDerivAt
    have hF : ∀ i, HasDerivAt (fun t => f (u n j t) i) (dEff (fun e => f e i) estar n j) t0 := by
      intro i
      exact ((hfdiff i).differentiableAt.comp t0 (hu_diff n j t0)).hasDerivAt
    have hsum : ∀ t, ∑ m, V m (u n j t m) =
        V n (Function.update (estar n) j t) + ∑ m ∈ Finset.univ.erase n, V m (estar m) := by
      intro t
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n)]
      congr 1
      · simp [u]
      · apply Finset.sum_congr rfl
        intro m hm
        simp [u, Function.update_of_ne (Finset.ne_of_mem_erase hm)]
    -- first best FOC
    have hFB : deriv (fun t => V n (Function.update (estar n) j t)) t0
        - pS * ∑ i, dEff (fun e => f e i) estar n j = 0 := by
      have hD : HasDerivAt (fun t => V n (Function.update (estar n) j t)
          + ∑ m ∈ Finset.univ.erase n, V m (estar m) - pS * ∑ i, f (u n j t) i)
          (deriv (fun t => V n (Function.update (estar n) j t)) t0
            - pS * ∑ i, dEff (fun e => f e i) estar n j) t0 :=
        (hV.add_const _).fun_sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hF i)).const_mul pS)
      have hmax : IsLocalMax (fun t => V n (Function.update (estar n) j t)
          + ∑ m ∈ Finset.univ.erase n, V m (estar m) - pS * ∑ i, f (u n j t) i) t0 := by
        filter_upwards [Ioo_mem_nhds (hmemIoo n j).1 (hmemIoo n j).2] with t ht
        have h1 := hfb.2 (u n j t) (hu_box n j t ⟨ht.1.le, ht.2.le⟩)
        have h2 : socialValue V f pS (u n j t) = V n (Function.update (estar n) j t)
            + ∑ m ∈ Finset.univ.erase n, V m (estar m) - pS * ∑ i, f (u n j t) i := by
          unfold socialValue; rw [hsum t]
        have h3 : socialValue V f pS estar = V n (Function.update (estar n) j t0)
            + ∑ m ∈ Finset.univ.erase n, V m (estar m) - pS * ∑ i, f (u n j t0) i := by
          have hu0' : u n j t0 = estar := hu0 n j
          have e3 := hsum t0
          rw [hu0'] at e3
          unfold socialValue
          rw [hu0', e3]
        rw [← h2, ← h3]
        exact h1
      exact hmax.hasDerivAt_eq_zero hD
    -- Nash FOC
    have hNE : deriv (fun t => V n (Function.update (estar n) j t)) t0
        - ∑ i, H n i * dEff (fun e => f e i) estar n j = 0 := by
      have hΦ : HasDerivAt (fun t => f (u n j t)) (fun i => dEff (fun e => f e i) estar n j) t0 :=
        hasDerivAt_pi.2 hF
      have hu0' : u n j t0 = estar := hu0 n j
      have hupd : Function.update (estar n) j t0 = estar n := Function.update_eq_self j (estar n)
      have hc := P2Aux.hasDerivAt_comp_foot (h n) (hdiff n) (fun t => f (u n j t)) _ t0 hΦ
      rw [hu0'] at hc
      have hD := hV.fun_sub hc
      have hmax : IsLocalMax (fun t => V n (Function.update (estar n) j t) - h n (f (u n j t)))
          t0 := by
        filter_upwards [Ioo_mem_nhds (hmemIoo n j).1 (hmemIoo n j).2] with t ht
        have hx : Function.update (estar n) j t ∈ firmBox A n := by
          intro k
          rcases eq_or_ne k j with rfl | hk
          · simpa using (⟨ht.1.le, ht.2.le⟩ : 0 ≤ t ∧ t ≤ A)
          · simpa [Function.update_of_ne hk] using hbox n k
        have h1 := hnash.2 n _ hx
        simp only [Function.update_self] at h1
        show _ ≤ V n (Function.update (estar n) j t0) - h n (f (u n j t0))
        rw [hu0', hupd]
        exact h1
      exact hmax.hasDerivAt_eq_zero hD
    have e1 : ∑ i, (pS - H n i) * dEff (fun e => f e i) estar n j
        = pS * ∑ i, dEff (fun e => f e i) estar n j
          - ∑ i, H n i * dEff (fun e => f e i) estar n j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e1]; linarith
  -- sum over the actions of each firm
  set D : ι → κ → ℝ := fun n i => ∑ j, dEff (fun e => f e i) estar n j with hDdef
  have hD0 : ∀ n i, D n i ≤ 0 := fun n i => Finset.sum_nonpos (fun j _ => hd n j i)
  have key2 : ∀ n, ∑ i, (pS - H n i) * (-D n i) = 0 := by
    intro n
    have : ∑ i, (pS - H n i) * (-D n i) = -∑ j, ∑ i, (pS - H n i) * dEff (fun e => f e i) estar n j := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _
      simp only [hDdef, Finset.mul_sum, mul_neg]
    rw [this, Finset.sum_eq_zero (fun j _ => key n j), neg_zero]
  -- conclude
  by_contra hnot
  have hle : ∀ i, ∑ n, H n i ≤ pS := by
    intro i
    by_contra hi
    exact hnot ⟨i, lt_of_not_ge hi⟩
  have Hle : ∀ n i, H n i ≤ pS := fun n i =>
    (Finset.single_le_sum (fun m _ => hH0 m i) (Finset.mem_univ n)).trans (hle i)
  obtain ⟨i0, hi0⟩ := hjoint
  have hpos : ∀ n, B n i0 = 1 → H n i0 = pS := by
    intro n hn
    have hneg : D n i0 < 0 := (hB estar hbox n i0).1 hn
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (sub_nonneg.2 (Hle n i)) (neg_nonneg.2 (hD0 n i)))).1 (key2 n) i0
      (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h1 | h1
    · linarith
    · linarith
  have hge : ∀ n, B n i0 * pS ≤ H n i0 := by
    intro n
    rcases hB01 n i0 with hb | hb
    · rw [hb, zero_mul]; exact hH0 n i0
    · rw [hb, one_mul, hpos n hb]
  have hsumge : (∑ n, B n i0) * pS ≤ ∑ n, H n i0 := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun n _ => hge n)
  have := hle i0
  nlinarith
