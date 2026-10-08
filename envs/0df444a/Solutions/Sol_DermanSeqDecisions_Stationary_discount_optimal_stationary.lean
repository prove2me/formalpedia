-- Prove2me | solution 1 for DermanSeqDecisions.Stationary.discount_optimal_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:30:09.928105+00:00
-- url     : https://prove2.me/submissions/3d7da226-df2f-48a2-992b-b778b43dbee7

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal
open SennottDP.AvgFinite


namespace DermanSeqDecisions.Stationary

lemma dso_tsum_len_succ {β : Type*} (F : List β → ℝ≥0∞) (n : ℕ) :
    (∑' h : List β, if h.length = n + 1 then F h else 0) =
      ∑' p : β, ∑' r : List β, if r.length = n then F (p :: r) else 0 := by
  have hinj : Function.Injective (fun x : β × List β => x.1 :: x.2) := by
    intro x y h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  have hsupp : (Function.support fun h : List β => if h.length = n + 1 then F h else 0) ⊆
      Set.range (fun x : β × List β => x.1 :: x.2) := by
    intro h hh
    cases h with
    | nil => simp at hh
    | cons p r => exact ⟨(p, r), rfl⟩
  rw [← hinj.tsum_eq hsupp]
  rw [ENNReal.tsum_prod (f := fun p r => if (p :: r).length = n + 1 then F (p :: r) else 0)]
  simp

section
variable {S : Type*} {Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}

noncomputable def dPsi (θ : Policy M) (i : S) (n : ℕ) (G : S → Act → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' r : List (S × Act), if r.length = n then
    ∑ j, ∑ a, histProb θ i r * prevWeight M i r j * θ.prob r j a * G j a else 0

noncomputable def dPhi (θ : Policy M) (i : S) (n : ℕ) (w : S → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' r : List (S × Act), if r.length = n then
    ∑ j, histProb θ i r * prevWeight M i r j * w j else 0

lemma dso_split (K : List (S × Act) → ℝ≥0∞) (n : ℕ) :
    (∑' h : List (S × Act), if h.length = n + 1 then K h else 0) =
      ∑' r : List (S × Act), if r.length = n then ∑ j, ∑ a, K ((j, a) :: r) else 0 := by
  rw [dso_tsum_len_succ, ENNReal.tsum_comm]
  congr 1
  ext r
  by_cases hr : r.length = n <;> simp [hr, tsum_fintype, Fintype.sum_prod_type]

lemma dso_expCost (θ : Policy M) (i : S) (n : ℕ) :
    expCost θ i n = dPsi θ i n (fun j a => (M.C j a : ℝ≥0∞)) := by
  unfold expCost dPsi
  rw [dso_split]
  rfl

lemma dso_phi_succ (θ : Policy M) (i : S) (n : ℕ) (w : S → ℝ≥0∞) :
    dPhi θ i (n + 1) w = dPsi θ i n (fun j a => ∑ k, M.P j a k * w k) := by
  unfold dPhi dPsi
  rw [dso_split]
  congr 1
  ext r
  split_ifs
  · simp only [histProb, prevWeight, Finset.mul_sum, mul_assoc]
  · rfl

lemma dso_phi_eq (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (n : ℕ)
    (w : S → ℝ≥0∞) : dPhi θ i n w = dPsi θ i n (fun j _ => w j) := by
  unfold dPhi dPsi
  congr 1
  ext r
  split_ifs
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := θ.prob_sum r j
    rw [hA] at h1
    calc histProb θ i r * prevWeight M i r j * w j
        = histProb θ i r * prevWeight M i r j * w j * ∑ a, θ.prob r j a := by rw [h1, mul_one]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  · rfl

lemma dso_psi_mono (θ : Policy M) (i : S) (n : ℕ) (G G' : S → Act → ℝ≥0∞)
    (h : ∀ j a, G j a ≤ G' j a) : dPsi θ i n G ≤ dPsi θ i n G' := by
  unfold dPsi
  refine ENNReal.tsum_le_tsum fun r => ?_
  split_ifs
  · gcongr with j _ a _
    exact h j a
  · exact le_rfl

lemma dso_psi_congr (θ : Policy M) (i : S) (n : ℕ) (G G' : S → Act → ℝ≥0∞)
    (h : ∀ r j a, θ.prob r j a * G j a = θ.prob r j a * G' j a) :
    dPsi θ i n G = dPsi θ i n G' := by
  unfold dPsi
  congr 1
  ext r
  split_ifs
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, h r j a, ← mul_assoc]
  · rfl

lemma dso_psi_add (θ : Policy M) (i : S) (n : ℕ) (G1 G2 : S → Act → ℝ≥0∞) (c : ℝ≥0∞) :
    dPsi θ i n (fun j a => G1 j a + c * G2 j a) = dPsi θ i n G1 + c * dPsi θ i n G2 := by
  unfold dPsi
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  congr 1
  ext r
  split_ifs
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  · simp

lemma dso_psi_smul (θ : Policy M) (i : S) (n : ℕ) (G : S → Act → ℝ≥0∞) (c : ℝ≥0∞) :
    dPsi θ i n (fun j a => c * G j a) = c * dPsi θ i n G := by
  have := dso_psi_add θ i n (fun _ _ => 0) G c
  simp only [zero_add] at this
  rw [this]
  have h0 : dPsi θ i n (fun _ _ => 0) = 0 := by simp [dPsi]
  rw [h0, zero_add]

lemma dso_phi_zero (θ : Policy M) (i : S) (w : S → ℝ≥0∞) : dPhi θ i 0 w = w i := by
  unfold dPhi
  rw [tsum_eq_single []]
  · simp only [histProb, prevWeight, if_true, one_mul, List.length_nil]
    rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
    simp
  · intro b hb
    have : b.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hb
    simp [this]

lemma dso_mass (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (n : ℕ) :
    dPhi θ i n (fun _ => 1) = 1 := by
  induction n with
  | zero => exact dso_phi_zero θ i _
  | succ n ih =>
    calc dPhi θ i (n + 1) (fun _ => 1) = dPsi θ i n (fun j a => ∑ k, M.P j a k * 1) :=
          dso_phi_succ θ i n _
      _ = dPsi θ i n (fun j _ => 1) := by
          congr 1
          funext j a
          simp only [mul_one]
          rw [← M.P_sum j a, tsum_fintype]
      _ = dPhi θ i n (fun _ => 1) := (dso_phi_eq hA θ i n _).symm
      _ = 1 := ih

/-- the one-step identity -/
lemma dso_step (θ : Policy M) (i : S) (n : ℕ) (α : ℝ) (V : S → ℝ≥0∞) :
    dPsi θ i n (fun j a => (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) =
      expCost θ i n + ENNReal.ofReal α * dPhi θ i (n + 1) V := by
  rw [dso_psi_add, dso_expCost, dso_phi_succ]

lemma dso_lower (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (α : ℝ)
    (V : S → ℝ≥0∞)
    (hb : ∀ j a, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) (n : ℕ) :
    V i ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal α ^ t * expCost θ i t
      + ENNReal.ofReal α ^ n * dPhi θ i n V := by
  induction n with
  | zero => simp [dso_phi_zero]
  | succ n ih =>
    refine ih.trans ?_
    have h1 : dPhi θ i n V ≤ expCost θ i n + ENNReal.ofReal α * dPhi θ i (n + 1) V := by
      rw [dso_phi_eq hA, ← dso_step]
      exact dso_psi_mono _ _ _ _ _ hb
    calc ∑ t ∈ Finset.range n, ENNReal.ofReal α ^ t * expCost θ i t
          + ENNReal.ofReal α ^ n * dPhi θ i n V
        ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal α ^ t * expCost θ i t
          + ENNReal.ofReal α ^ n * (expCost θ i n + ENNReal.ofReal α * dPhi θ i (n + 1) V) := by
          gcongr
      _ = _ := by
          rw [Finset.sum_range_succ, pow_succ, mul_add, add_assoc, mul_assoc]

lemma dso_upper (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (α : ℝ)
    (V : S → ℝ≥0∞)
    (hb : ∀ r j a, θ.prob r j a * V j =
      θ.prob r j a * ((M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k)) (n : ℕ) :
    V i = ∑ t ∈ Finset.range n, ENNReal.ofReal α ^ t * expCost θ i t
      + ENNReal.ofReal α ^ n * dPhi θ i n V := by
  induction n with
  | zero => simp [dso_phi_zero]
  | succ n ih =>
    rw [ih]
    have h1 : dPhi θ i n V = expCost θ i n + ENNReal.ofReal α * dPhi θ i (n + 1) V := by
      rw [dso_phi_eq hA, ← dso_step]
      exact dso_psi_congr _ _ _ _ _ hb
    rw [h1, Finset.sum_range_succ, pow_succ, mul_add, add_assoc, mul_assoc]

end


section
variable {S : Type*} {Act : Type*} [Fintype S] [Nonempty S] [Fintype Act] [Nonempty Act]
  (M : MDC S Act)

lemma dso_P_ne_top (j : S) (a : Act) (k : S) : M.P j a k ≠ ⊤ :=
  ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top (by rw [← M.P_sum j a]; exact ENNReal.le_tsum k)

lemma dso_P_sum (j : S) (a : Act) : ∑ k, M.P j a k = 1 := by
  rw [← M.P_sum j a, tsum_fintype]

noncomputable def dpr (j : S) (a : Act) (k : S) : ℝ := (M.P j a k).toReal

lemma dso_pr_nonneg (j : S) (a : Act) (k : S) : 0 ≤ dpr M j a k := ENNReal.toReal_nonneg

lemma dso_pr_sum (j : S) (a : Act) : ∑ k, dpr M j a k = 1 := by
  unfold dpr
  rw [← ENNReal.toReal_sum (fun k _ => dso_P_ne_top M j a k), dso_P_sum]
  simp

noncomputable def dBop (α : ℝ) (u : S → ℝ) : S → ℝ := fun j =>
  Finset.univ.inf' Finset.univ_nonempty
    (fun a => (M.C j a : ℝ) + α * ∑ k, dpr M j a k * u k)

lemma dso_key (α : ℝ) (hα : 0 ≤ α) (u w : S → ℝ) (j : S) :
    dBop M α u j ≤ dBop M α w j + α * dist u w := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Act))
    (fun a => (M.C j a : ℝ) + α * ∑ k, dpr M j a k * w k)
  have h1 : dBop M α u j ≤ (M.C j a : ℝ) + α * ∑ k, dpr M j a k * u k :=
    Finset.inf'_le _ (Finset.mem_univ a)
  have h2 : dBop M α w j = (M.C j a : ℝ) + α * ∑ k, dpr M j a k * w k := ha
  have h3 : ∑ k, dpr M j a k * u k ≤ ∑ k, dpr M j a k * w k + dist u w := by
    have : ∑ k, dpr M j a k * u k ≤ ∑ k, dpr M j a k * (w k + dist u w) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (dso_pr_nonneg M j a k)
      have := dist_le_pi_dist u w k
      rw [Real.dist_eq] at this
      linarith [le_abs_self (u k - w k)]
    rw [show ∑ k, dpr M j a k * (w k + dist u w) = ∑ k, dpr M j a k * w k
      + (∑ k, dpr M j a k) * dist u w by rw [Finset.sum_mul, ← Finset.sum_add_distrib]; congr 1; ext k; ring] at this
    rw [dso_pr_sum, one_mul] at this
    exact this
  rw [h2]
  nlinarith

lemma dso_contract (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    ContractingWith ⟨α, h0.le⟩ (dBop M α) := by
  refine ⟨?_, ?_⟩
  · exact NNReal.coe_lt_coe.1 (show α < ((1 : ℝ≥0) : ℝ) by simpa using h1)
  · refine LipschitzWith.of_dist_le_mul fun u w => ?_
    show dist _ _ ≤ α * dist u w
    refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
    rw [Real.dist_eq, abs_le]
    have h1 := dso_key M α h0.le u w j
    have h2 := dso_key M α h0.le w u j
    rw [dist_comm w u] at h2
    constructor <;> linarith

lemma dso_G_eq (α : ℝ) (hα : 0 ≤ α) (v : S → ℝ) (hv : ∀ j, 0 ≤ v j) (j : S) (a : Act) :
    (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * ENNReal.ofReal (v k) =
      ENNReal.ofReal ((M.C j a : ℝ) + α * ∑ k, dpr M j a k * v k) := by
  have hs : 0 ≤ ∑ k, dpr M j a k * v k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (dso_pr_nonneg M j a k) (hv k)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hα,
    ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (dso_pr_nonneg M j a k) (hv k)),
    ENNReal.ofReal_coe_nnreal]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_mul (dso_pr_nonneg M j a k), dpr, ENNReal.ofReal_toReal (dso_P_ne_top M j a k)]

/-- main: existence of value V and greedy stationary f. -/
theorem dso_main (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∃ V : S → ℝ≥0∞,
      (∀ j, V j = (M.C j (f.f j) : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j (f.f j) k * V k) ∧
      (∀ j a, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) ∧
      (∀ θ : Policy M, ∀ i, V i ≤ discCost θ α i) ∧
      (∀ i, discCost f.toPolicy α i ≤ V i) := by
  have hc := dso_contract M α hα.1 hα.2
  set v := ContractingWith.fixedPoint (dBop M α) hc with hvdef
  have hfix : dBop M α v = v := ContractingWith.fixedPoint_isFixedPt hc
  clear_value v
  -- nonneg
  have hv0 : ∀ j, 0 ≤ v j := by
    obtain ⟨j0, hj0⟩ := Finite.exists_min v
    have hle : α * v j0 ≤ v j0 := by
      have : α * v j0 ≤ dBop M α v j0 := by
        apply Finset.le_inf'
        intro a _
        have hs : v j0 ≤ ∑ k, dpr M j0 a k * v k := by
          calc v j0 = ∑ k, dpr M j0 a k * v j0 := by rw [← Finset.sum_mul, dso_pr_sum, one_mul]
            _ ≤ _ := Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_left (hj0 k) (dso_pr_nonneg M j0 a k)
        have : (0:ℝ) ≤ M.C j0 a := NNReal.coe_nonneg _
        nlinarith [hα.1]
      rw [hfix] at this
      exact this
    have : 0 ≤ v j0 := by nlinarith [hα.2]
    intro j
    exact this.trans (hj0 j)
  have hex : ∀ j, ∃ a ∈ (Finset.univ : Finset Act), dBop M α v j =
      (M.C j a : ℝ) + α * ∑ k, dpr M j a k * v k := fun j =>
    Finset.exists_mem_eq_inf' Finset.univ_nonempty _
  choose fs _ hfs using hex
  let f : StationaryPolicy M := ⟨fs, fun i => by rw [hA]; exact Finset.mem_univ _⟩
  let V : S → ℝ≥0∞ := fun j => ENNReal.ofReal (v j)
  have hVa : ∀ j, V j = (M.C j (f.f j) : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j (f.f j) k * V k := by
    intro j
    rw [dso_G_eq M α hα.1.le v hv0]
    show ENNReal.ofReal (v j) = _
    rw [← hfs j]
    conv_lhs => rw [← hfix]
  have hVb : ∀ j a, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k := by
    intro j a
    rw [dso_G_eq M α hα.1.le v hv0]
    apply ENNReal.ofReal_le_ofReal
    conv_lhs => rw [← hfix]
    exact Finset.inf'_le _ (Finset.mem_univ a)
  refine ⟨f, V, hVa, hVb, ?_, ?_⟩
  · intro θ i
    set B : ℝ≥0∞ := ENNReal.ofReal (∑ j, v j)
    have hB : ∀ j, V j ≤ B := fun j => ENNReal.ofReal_le_ofReal
      (Finset.single_le_sum (fun k _ => hv0 k) (Finset.mem_univ j))
    have hBt : B ≠ ⊤ := ENNReal.ofReal_ne_top
    have hn : ∀ n, V i ≤ discCost θ α i + ENNReal.ofReal α ^ n * B := by
      intro n
      refine (dso_lower hA θ i α V hVb n).trans ?_
      gcongr
      · unfold discCost
        exact ENNReal.sum_le_tsum _
      · calc dPhi θ i n V ≤ dPhi θ i n (fun _ => B) := by
              rw [dso_phi_eq hA, dso_phi_eq hA]
              exact dso_psi_mono _ _ _ _ _ fun j _ => hB j
          _ = B * dPhi θ i n (fun _ => 1) := by
              rw [dso_phi_eq hA, dso_phi_eq hA, ← dso_psi_smul]
              simp
          _ = B := by rw [dso_mass hA, mul_one]
    have ht : Filter.Tendsto (fun n => discCost θ α i + ENNReal.ofReal α ^ n * B)
        Filter.atTop (nhds (discCost θ α i + 0 * B)) := by
      apply tendsto_const_nhds.add
      · apply ENNReal.Tendsto.mul_const
        · exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
            (by rw [ENNReal.ofReal_lt_one]; exact hα.2)
        · exact Or.inr hBt
    rw [zero_mul, add_zero] at ht
    exact ge_of_tendsto' ht hn
  · intro i
    unfold discCost
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    rw [dso_upper hA f.toPolicy i α V ?_ n]
    · exact le_self_add
    · intro r j a
      simp only [StationaryPolicy.toPolicy]
      split_ifs with h
      · subst h
        rw [one_mul, one_mul]
        exact hVa j
      · simp
end


section
variable {S : Type*} {Act : Type*} [Fintype S] [Nonempty S] [Fintype Act] [Nonempty Act]

theorem dos_core (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      discCost f.toPolicy α i ≤ discCost θ α i := by
  obtain ⟨f, V, -, -, h1, h2⟩ := dso_main M hA α hα
  exact ⟨f, fun θ i => (h2 i).trans (h1 θ i)⟩

theorem fe_core (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (i : S) :
    IsLeast
      {x : ℝ≥0∞ | ∃ D : Act → ℝ≥0∞, ∑ k, D k = 1 ∧
        x = ∑ k, D k * ((M.C i k : ℝ≥0∞) + ENNReal.ofReal α * ∑ j, M.P i k j * discValue M α j)}
      (discValue M α i) := by
  classical
  obtain ⟨f, V, ha, hb, h1, h2⟩ := dso_main M hA α hα
  have hV : discValue M α = V := funext fun j =>
    le_antisymm (iInf_le_of_le f.toPolicy (h2 j)) (le_iInf fun θ => h1 θ j)
  rw [hV]
  constructor
  · refine ⟨fun k => if k = f.f i then 1 else 0, by simp, ?_⟩
    rw [Finset.sum_eq_single (f.f i)]
    · simpa using ha i
    · intro b _ hb
      simp [hb]
    · simp
  · rintro x ⟨D, hD, rfl⟩
    calc V i = ∑ k, D k * V i := by rw [← Finset.sum_mul, hD, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun k _ => by gcongr; exact hb i k

lemma dso_sp_ext {M : MDC S Act} (p q : StationaryPolicy M) (h : p.f = q.f) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem cos_core (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ∃ f : StationaryPolicy M, ∃ αs : ℕ → ℝ,
      (∀ v, αs v ∈ Set.Ioo (0 : ℝ) 1) ∧ Filter.Tendsto αs Filter.atTop (nhds 1) ∧
      ∀ v, ∀ θ : Policy M, ∀ i : S,
        discCost f.toPolicy (αs v) i ≤ discCost θ (αs v) i := by
  let a : ℕ → ℝ := fun m => 1 - 1 / (((m + 1 : ℕ) : ℝ) + 1)
  have ha : ∀ m, a m ∈ Set.Ioo (0 : ℝ) 1 := by
    intro m
    have hpos : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    constructor
    · have : 1 / (((m + 1 : ℕ) : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      simp only [a]; linarith
    · have : 0 < 1 / (((m + 1 : ℕ) : ℝ) + 1) := by positivity
      simp only [a]; linarith
  have hat : Filter.Tendsto a Filter.atTop (nhds 1) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    have := (tendsto_const_nhds (x := (1:ℝ))).sub h0
    simpa [a, Function.comp_def] using this
  have hex : ∀ m, ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      discCost f.toPolicy (a m) i ≤ discCost θ (a m) i := fun m => dos_core M hA (a m) (ha m)
  choose fv hfv using hex
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber (fun m => (fv m).f)
  rw [Set.infinite_coe_iff] at hy
  have hfr : ∃ᶠ m in Filter.atTop, (fv m).f = y := Nat.frequently_atTop_iff_infinite.2 hy
  obtain ⟨φ, hφ, hφy⟩ := Filter.extraction_of_frequently_atTop hfr
  refine ⟨fv (φ 0), fun n => a (φ n), fun n => ha (φ n), hat.comp hφ.tendsto_atTop, ?_⟩
  intro n θ i
  have : fv (φ 0) = fv (φ n) := dso_sp_ext _ _ ((hφy 0).trans (hφy n).symm)
  rw [this]
  exact hfv (φ n) θ i

end

end DermanSeqDecisions.Stationary

open DermanSeqDecisions.Stationary


theorem solution {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      discCost f.toPolicy α i ≤ discCost θ α i := by
  exact dos_core M hA α hα
