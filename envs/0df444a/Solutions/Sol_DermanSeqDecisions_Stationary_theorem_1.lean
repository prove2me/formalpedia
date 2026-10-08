-- Prove2me | solution 1 for DermanSeqDecisions.Stationary.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:43:23.556844+00:00
-- url     : https://prove2.me/submissions/289c8d4a-9498-4a12-9821-c75d6b8d2a6c

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_DermanSeqDecisions_Stationary_totalCost

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

lemma dso_psi_mono' (θ : Policy M) (i : S) (n : ℕ) (G G' : S → Act → ℝ≥0∞)
    (h : ∀ r j a, θ.prob r j a * G j a ≤ θ.prob r j a * G' j a) :
    dPsi θ i n G ≤ dPsi θ i n G' := by
  unfold dPsi
  refine ENNReal.tsum_le_tsum fun r => ?_
  split_ifs
  · refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ => ?_
    have := mul_le_mul_of_nonneg_left (h r j a) (bot_le : ⊥ ≤ histProb θ i r * prevWeight M i r j)
    simpa only [mul_assoc] using this
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
    (hb : ∀ r j a, θ.prob r j a * V j ≤
      θ.prob r j a * ((M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k)) (n : ℕ) :
    V i ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal α ^ t * expCost θ i t
      + ENNReal.ofReal α ^ n * dPhi θ i n V := by
  induction n with
  | zero => simp [dso_phi_zero]
  | succ n ih =>
    refine ih.trans ?_
    have h1 : dPhi θ i n V ≤ expCost θ i n + ENNReal.ofReal α * dPhi θ i (n + 1) V := by
      rw [dso_phi_eq hA, ← dso_step]
      exact dso_psi_mono' _ _ _ _ _ hb
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

noncomputable def dBop (A : S → Finset Act) (hAn : ∀ j, (A j).Nonempty) (α : ℝ)
    (u : S → ℝ) : S → ℝ := fun j =>
  (A j).inf' (hAn j) (fun a => (M.C j a : ℝ) + α * ∑ k, dpr M j a k * u k)

lemma dso_key (A : S → Finset Act) (hAn : ∀ j, (A j).Nonempty) (α : ℝ) (hα : 0 ≤ α)
    (u w : S → ℝ) (j : S) :
    dBop M A hAn α u j ≤ dBop M A hAn α w j + α * dist u w := by
  obtain ⟨a, haA, ha⟩ := Finset.exists_mem_eq_inf' (hAn j)
    (fun a => (M.C j a : ℝ) + α * ∑ k, dpr M j a k * w k)
  have h1 : dBop M A hAn α u j ≤ (M.C j a : ℝ) + α * ∑ k, dpr M j a k * u k :=
    Finset.inf'_le _ haA
  have h2 : dBop M A hAn α w j = (M.C j a : ℝ) + α * ∑ k, dpr M j a k * w k := ha
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

lemma dso_contract (A : S → Finset Act) (hAn : ∀ j, (A j).Nonempty) (α : ℝ) (h0 : 0 < α)
    (h1 : α < 1) : ContractingWith ⟨α, h0.le⟩ (dBop M A hAn α) := by
  refine ⟨?_, ?_⟩
  · exact NNReal.coe_lt_coe.1 (show α < ((1 : ℝ≥0) : ℝ) by simpa using h1)
  · refine LipschitzWith.of_dist_le_mul fun u w => ?_
    show dist _ _ ≤ α * dist u w
    refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
    rw [Real.dist_eq, abs_le]
    have h1 := dso_key M A hAn α h0.le u w j
    have h2 := dso_key M A hAn α h0.le w u j
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

lemma dso_sumP (j : S) (a : Act) (v : S → ℝ) (hv : ∀ j, 0 ≤ v j) :
    ∑ k, M.P j a k * ENNReal.ofReal (v k) = ENNReal.ofReal (∑ k, dpr M j a k * v k) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (dso_pr_nonneg M j a k) (hv k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_mul (dso_pr_nonneg M j a k), dpr, ENNReal.ofReal_toReal (dso_P_ne_top M j a k)]

theorem dso_gen (A : S → Finset Act) (hAn : ∀ j, (A j).Nonempty) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ fs : S → Act, (∀ j, fs j ∈ A j) ∧ ∃ V : S → ℝ≥0∞, (∀ j, V j ≠ ⊤) ∧
      (∀ j, V j = (M.C j (fs j) : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j (fs j) k * V k) ∧
      (∀ j, ∀ a ∈ A j, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) := by
  have hc := dso_contract M A hAn α hα.1 hα.2
  set v := ContractingWith.fixedPoint (dBop M A hAn α) hc with hvdef
  have hfix : dBop M A hAn α v = v := ContractingWith.fixedPoint_isFixedPt hc
  clear_value v
  have hv0 : ∀ j, 0 ≤ v j := by
    obtain ⟨j0, hj0⟩ := Finite.exists_min v
    have hle : α * v j0 ≤ v j0 := by
      have : α * v j0 ≤ dBop M A hAn α v j0 := by
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
  have hex : ∀ j, ∃ a ∈ A j, dBop M A hAn α v j =
      (M.C j a : ℝ) + α * ∑ k, dpr M j a k * v k := fun j =>
    Finset.exists_mem_eq_inf' (hAn j) _
  choose fs hfsA hfs using hex
  refine ⟨fs, hfsA, fun j => ENNReal.ofReal (v j), fun j => ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro j
    rw [dso_G_eq M α hα.1.le v hv0]
    rw [← hfs j]
    conv_lhs => rw [← hfix]
  · intro j a ha
    rw [dso_G_eq M α hα.1.le v hv0]
    apply ENNReal.ofReal_le_ofReal
    conv_lhs => rw [← hfix]
    exact Finset.inf'_le _ ha

lemma dso_lb (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (V : S → ℝ≥0∞) (hVt : ∀ j, V j ≠ ⊤)
    (hb : ∀ r j a, θ.prob r j a * V j ≤
      θ.prob r j a * ((M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k)) :
    V i ≤ discCost θ α i := by
  set B : ℝ≥0∞ := ∑ j, V j
  have hB : ∀ j, V j ≤ B := fun j => Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)
  have hBt : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => hVt j
  have hn : ∀ n, V i ≤ discCost θ α i + ENNReal.ofReal α ^ n * B := by
    intro n
    refine (dso_lower hA θ i α V hb n).trans ?_
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

lemma dso_ub (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (α : ℝ)
    (V : S → ℝ≥0∞)
    (hb : ∀ r j a, θ.prob r j a * V j =
      θ.prob r j a * ((M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k)) :
    discCost θ α i ≤ V i := by
  unfold discCost
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  rw [dso_upper hA θ i α V hb n]
  exact le_self_add

omit [Nonempty S] [Nonempty Act] in
lemma dso_stat_w (f : StationaryPolicy M) (V : S → ℝ≥0∞) (G : S → Act → ℝ≥0∞)
    (h : ∀ j, V j = G j (f.f j)) : ∀ r j a, f.toPolicy.prob r j a * V j =
      f.toPolicy.prob r j a * G j a := by
  intro r j a
  simp only [StationaryPolicy.toPolicy]
  split_ifs with h'
  · subst h'
    rw [one_mul, one_mul]
    exact h j
  · simp

omit [Nonempty S] [Nonempty Act] in
lemma dso_stat_wle (f : StationaryPolicy M) (V : S → ℝ≥0∞) (G : S → Act → ℝ≥0∞)
    (h : ∀ j, G j (f.f j) ≤ V j) : ∀ r j a, f.toPolicy.prob r j a * G j a ≤
      f.toPolicy.prob r j a * V j := by
  intro r j a
  simp only [StationaryPolicy.toPolicy]
  split_ifs with h'
  · subst h'
    rw [one_mul, one_mul]
    exact h j
  · simp

/-- main: existence of value V and greedy stationary f. -/
theorem dso_main (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∃ V : S → ℝ≥0∞,
      (∀ j, V j = (M.C j (f.f j) : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j (f.f j) k * V k) ∧
      (∀ j a, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) ∧
      (∀ θ : Policy M, ∀ i, V i ≤ discCost θ α i) ∧
      (∀ i, discCost f.toPolicy α i ≤ V i) := by
  obtain ⟨fs, -, V, hVt, hVa, hVb⟩ := dso_gen M (fun _ => Finset.univ)
    (fun _ => Finset.univ_nonempty) α hα
  let f : StationaryPolicy M := ⟨fs, fun i => by rw [hA]; exact Finset.mem_univ _⟩
  have hVb' : ∀ j a, V j ≤ (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k :=
    fun j a => hVb j a (Finset.mem_univ a)
  refine ⟨f, V, hVa, hVb', ?_, ?_⟩
  · intro θ i
    exact dso_lb M hA θ i α hα V hVt fun r j a => by gcongr; exact hVb' j a
  · intro i
    exact dso_ub M hA f.toPolicy i α V (dso_stat_w M f V _ hVa)

/-- the value of a stationary policy satisfies its fixed point equation -/
theorem dso_stat_eq (hA : ∀ i, M.A i = Finset.univ) (f : StationaryPolicy M) (α : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ j, discCost f.toPolicy α j ≠ ⊤) ∧
    ∀ j, discCost f.toPolicy α j = (M.C j (f.f j) : ℝ≥0∞) +
      ENNReal.ofReal α * ∑ k, M.P j (f.f j) k * discCost f.toPolicy α k := by
  obtain ⟨fs, hfs, V, hVt, hVa, -⟩ := dso_gen M (fun j => {f.f j})
    (fun _ => Finset.singleton_nonempty _) α hα
  have hfs' : ∀ j, fs j = f.f j := fun j => Finset.mem_singleton.1 (hfs j)
  simp only [hfs'] at hVa
  have hE : ∀ j, discCost f.toPolicy α j = V j := fun j =>
    le_antisymm (dso_ub M hA f.toPolicy j α V (dso_stat_w M f V _ hVa))
      (dso_lb M hA f.toPolicy j α hα V hVt
        (fun r j a => (dso_stat_w M f V
          (fun j a => (M.C j a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P j a k * V k) hVa r j a).le))
  have hE' : (fun j => discCost f.toPolicy α j) = V := funext hE
  refine ⟨fun j => (hE j).symm ▸ hVt j, fun j => ?_⟩
  simp only [hE]
  exact hVa j

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


section
variable {S : Type*} {Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}

lemma dso_phi_mono (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (n : ℕ)
    (w w' : S → ℝ≥0∞) (h : ∀ j, w j ≤ w' j) : dPhi θ i n w ≤ dPhi θ i n w' := by
  rw [dso_phi_eq hA, dso_phi_eq hA]
  exact dso_psi_mono _ _ _ _ _ fun j _ => h j

lemma dso_phi_const (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (n : ℕ)
    (c : ℝ≥0∞) : dPhi θ i n (fun _ => c) = c := by
  calc dPhi θ i n (fun _ => c) = c * dPhi θ i n (fun _ => 1) := by
        rw [dso_phi_eq hA, dso_phi_eq hA, ← dso_psi_smul]
        simp
    _ = c := by rw [dso_mass hA, mul_one]

lemma dso_harm (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (w : S → ℝ≥0∞)
    (h : ∀ r j a, θ.prob r j a * w j = θ.prob r j a * ∑ k, M.P j a k * w k) (n : ℕ) :
    dPhi θ i n w = w i := by
  induction n with
  | zero => exact dso_phi_zero θ i w
  | succ n ih =>
    rw [dso_phi_succ, ← ih, dso_phi_eq hA]
    exact (dso_psi_congr _ _ _ _ _ h).symm

lemma dso_subharm (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (w : S → ℝ≥0∞)
    (h : ∀ j a, w j ≤ ∑ k, M.P j a k * w k) (n : ℕ) : w i ≤ dPhi θ i n w := by
  induction n with
  | zero => exact (dso_phi_zero θ i w).ge
  | succ n ih =>
    refine ih.trans ?_
    rw [dso_phi_succ, dso_phi_eq hA]
    exact dso_psi_mono _ _ _ _ _ h

lemma dso_step1 (θ : Policy M) (i : S) (n : ℕ) (V : S → ℝ≥0∞) :
    dPsi θ i n (fun j a => (M.C j a : ℝ≥0∞) + ∑ k, M.P j a k * V k) =
      expCost θ i n + dPhi θ i (n + 1) V := by
  have := dso_step θ i n 1 V
  simpa using this

lemma dso_step1' (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (n : ℕ)
    (V U : S → ℝ≥0∞) :
    dPhi θ i n V + dPhi θ i (n + 1) U = dPsi θ i n (fun j a => V j + ∑ k, M.P j a k * U k) := by
  rw [dso_phi_eq hA, dso_phi_succ,
    ← one_mul (dPsi θ i n (fun j a => ∑ k, M.P j a k * U k)), ← dso_psi_add]
  simp only [one_mul]

lemma dso_tele_le (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (V U : S → ℝ≥0∞)
    (h : ∀ r j a, θ.prob r j a * (V j + ∑ k, M.P j a k * U k) ≤
      θ.prob r j a * ((M.C j a : ℝ≥0∞) + ∑ k, M.P j a k * V k)) (n : ℕ) :
    V i + ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U ≤ horizonCost θ n i + dPhi θ i n V := by
  induction n with
  | zero => simp [horizonCost, dso_phi_zero]
  | succ n ih =>
    have key : dPhi θ i n V + dPhi θ i (n + 1) U ≤ expCost θ i n + dPhi θ i (n + 1) V := by
      rw [dso_step1' hA, ← dso_step1]
      exact dso_psi_mono' _ _ _ _ _ h
    calc V i + ∑ t ∈ Finset.range (n + 1), dPhi θ i (t + 1) U
        = (V i + ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U) + dPhi θ i (n + 1) U := by
          rw [Finset.sum_range_succ, add_assoc]
      _ ≤ (horizonCost θ n i + dPhi θ i n V) + dPhi θ i (n + 1) U := by gcongr
      _ = horizonCost θ n i + (dPhi θ i n V + dPhi θ i (n + 1) U) := add_assoc _ _ _
      _ ≤ horizonCost θ n i + (expCost θ i n + dPhi θ i (n + 1) V) := by gcongr
      _ = horizonCost θ (n + 1) i + dPhi θ i (n + 1) V := by
          rw [horizonCost, horizonCost, Finset.sum_range_succ, add_assoc]

lemma dso_tele_ge (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) (V U : S → ℝ≥0∞)
    (h : ∀ r j a, θ.prob r j a * ((M.C j a : ℝ≥0∞) + ∑ k, M.P j a k * V k) ≤
      θ.prob r j a * (V j + ∑ k, M.P j a k * U k)) (n : ℕ) :
    horizonCost θ n i + dPhi θ i n V ≤ V i + ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U := by
  induction n with
  | zero => simp [horizonCost, dso_phi_zero]
  | succ n ih =>
    have key : expCost θ i n + dPhi θ i (n + 1) V ≤ dPhi θ i n V + dPhi θ i (n + 1) U := by
      rw [dso_step1' hA, ← dso_step1]
      exact dso_psi_mono' _ _ _ _ _ h
    calc horizonCost θ (n + 1) i + dPhi θ i (n + 1) V
        = horizonCost θ n i + (expCost θ i n + dPhi θ i (n + 1) V) := by
          rw [horizonCost, horizonCost, Finset.sum_range_succ, add_assoc]
      _ ≤ horizonCost θ n i + (dPhi θ i n V + dPhi θ i (n + 1) U) := by gcongr
      _ = (horizonCost θ n i + dPhi θ i n V) + dPhi θ i (n + 1) U := (add_assoc _ _ _).symm
      _ ≤ (V i + ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U) + dPhi θ i (n + 1) U := by gcongr
      _ = V i + ∑ t ∈ Finset.range (n + 1), dPhi θ i (t + 1) U := by
          rw [Finset.sum_range_succ, add_assoc]

lemma dso_stat_w2 (f : StationaryPolicy M) (G H : S → Act → ℝ≥0∞)
    (h : ∀ j, G j (f.f j) ≤ H j (f.f j)) : ∀ r j a, f.toPolicy.prob r j a * G j a ≤
      f.toPolicy.prob r j a * H j a := by
  intro r j a
  simp only [StationaryPolicy.toPolicy]
  split_ifs with h'
  · subst h'
    rw [one_mul, one_mul]
    exact h j
  · simp

lemma dso_stat_w3 (f : StationaryPolicy M) (G H : S → Act → ℝ≥0∞)
    (h : ∀ j, G j (f.f j) = H j (f.f j)) : ∀ r j a, f.toPolicy.prob r j a * G j a =
      f.toPolicy.prob r j a * H j a := by
  intro r j a
  simp only [StationaryPolicy.toPolicy]
  split_ifs with h'
  · subst h'
    rw [one_mul, one_mul]
    exact h j
  · simp

end

lemma dso_avg_le (s : ℕ → ℝ≥0∞) (A L : ℝ≥0∞) (hA : A ≠ ⊤) (h : ∀ n : ℕ, s n ≤ A + n * L) :
    Filter.limsup (fun n : ℕ => s n / (n : ℝ≥0∞)) Filter.atTop ≤ L := by
  have ev : ∀ᶠ n : ℕ in Filter.atTop, s n / (n : ℝ≥0∞) ≤ A * (n : ℝ≥0∞)⁻¹ + L := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
    calc s n / (n : ℝ≥0∞) ≤ (A + n * L) / n := ENNReal.div_le_div_right (h n) _
      _ = A / n + n * L / n := ENNReal.add_div
      _ = A * (n : ℝ≥0∞)⁻¹ + L := by
          rw [div_eq_mul_inv, mul_comm (n : ℝ≥0∞) L,
            ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
  have ht : Filter.Tendsto (fun n : ℕ => A * (n : ℝ≥0∞)⁻¹ + L) Filter.atTop (nhds (A * 0 + L)) :=
    (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hA)).add
      tendsto_const_nhds
  rw [mul_zero, zero_add] at ht
  calc _ ≤ Filter.limsup (fun n : ℕ => A * (n : ℝ≥0∞)⁻¹ + L) Filter.atTop :=
        Filter.limsup_le_limsup ev
    _ = L := ht.limsup_eq

lemma dso_avg_ge (s : ℕ → ℝ≥0∞) (B L : ℝ≥0∞) (hB : B ≠ ⊤) (h : ∀ n : ℕ, n * L ≤ s n + B) :
    L ≤ Filter.limsup (fun n : ℕ => s n / (n : ℝ≥0∞)) Filter.atTop := by
  have ev : ∀ᶠ n : ℕ in Filter.atTop, L ≤ s n / (n : ℝ≥0∞) + B * (n : ℝ≥0∞)⁻¹ := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
    calc L = n * L / n := by
          rw [mul_comm (n : ℝ≥0∞) L, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
      _ ≤ (s n + B) / n := ENNReal.div_le_div_right (h n) _
      _ = s n / n + B / n := ENNReal.add_div
      _ = _ := by rw [div_eq_mul_inv B]
  have ht : Filter.Tendsto (fun n : ℕ => B * (n : ℝ≥0∞)⁻¹) Filter.atTop (nhds (B * 0)) :=
    ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hB)
  rw [mul_zero] at ht
  calc L = Filter.limsup (fun _ : ℕ => L) Filter.atTop := Filter.limsup_const L |>.symm
    _ ≤ Filter.limsup (fun n : ℕ => s n / (n : ℝ≥0∞) + B * (n : ℝ≥0∞)⁻¹) Filter.atTop :=
        Filter.limsup_le_limsup ev
    _ = _ := ENNReal.limsup_add_of_right_tendsto_zero ht (fun n : ℕ => s n / (n : ℝ≥0∞))


section
variable {S : Type*} {Act : Type*} [Fintype S] [Nonempty S] [Fintype Act] [Nonempty Act]

lemma dso_rhs_nonneg (M : MDC S Act) (α : ℝ) (hα : 0 ≤ α) (x : S → ℝ) (hx : ∀ j, 0 ≤ x j)
    (j : S) (a : Act) : 0 ≤ (M.C j a : ℝ) + α * ∑ k, dpr M j a k * x k :=
  add_nonneg (NNReal.coe_nonneg _)
    (mul_nonneg hα (Finset.sum_nonneg fun k _ => mul_nonneg (dso_pr_nonneg M j a k) (hx k)))

lemma dso_psum_nonneg (M : MDC S Act) (x : S → ℝ) (hx : ∀ j, 0 ≤ x j) (j : S) (a : Act) :
    0 ≤ ∑ k, dpr M j a k * x k :=
  Finset.sum_nonneg fun k _ => mul_nonneg (dso_pr_nonneg M j a k) (hx k)

theorem t1_core (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ∃ f : StationaryPolicy M,
      (∀ θ : Policy M, ∀ i : S, avgCost f.toPolicy i ≤ avgCost θ i) ∧
      (∀ θ : Policy M, ∀ i : S,
        DermanSeqDecisions.Stationary.totalCost f.toPolicy i ≤
          DermanSeqDecisions.Stationary.totalCost θ i) := by
  obtain ⟨f, αs, hαs, hlim, hopt⟩ := cos_core M hA
  refine ⟨f, ?_, ?_⟩
  swap
  · -- total cost
    intro θ i
    unfold DermanSeqDecisions.Stationary.totalCost
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    have hb : ∀ v, ENNReal.ofReal (αs v) ^ N * ∑ t ∈ Finset.range N, expCost f.toPolicy i t ≤
        ∑' t, expCost θ i t := by
      intro v
      have hle1 : ENNReal.ofReal (αs v) ≤ 1 := by
        rw [ENNReal.ofReal_le_one]; exact (hαs v).2.le
      calc ENNReal.ofReal (αs v) ^ N * ∑ t ∈ Finset.range N, expCost f.toPolicy i t
          = ∑ t ∈ Finset.range N, ENNReal.ofReal (αs v) ^ N * expCost f.toPolicy i t :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ t ∈ Finset.range N, ENNReal.ofReal (αs v) ^ t * expCost f.toPolicy i t := by
            refine Finset.sum_le_sum fun t ht => ?_
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_of_le_one bot_le hle1 (Finset.mem_range.1 ht).le) bot_le
        _ ≤ discCost f.toPolicy (αs v) i := ENNReal.sum_le_tsum _
        _ ≤ discCost θ (αs v) i := hopt v θ i
        _ ≤ ∑' t, expCost θ i t := by
            unfold discCost
            refine ENNReal.tsum_le_tsum fun t => ?_
            calc ENNReal.ofReal (αs v) ^ t * expCost θ i t ≤ 1 * expCost θ i t := by
                  exact mul_le_mul_of_nonneg_right (pow_le_one₀ bot_le hle1) bot_le
              _ = _ := one_mul _
    have ht : Filter.Tendsto (fun v => ENNReal.ofReal (αs v) ^ N *
        ∑ t ∈ Finset.range N, expCost f.toPolicy i t) Filter.atTop
        (nhds (ENNReal.ofReal 1 ^ N * ∑ t ∈ Finset.range N, expCost f.toPolicy i t)) := by
      apply ENNReal.Tendsto.mul_const
      · exact ENNReal.Tendsto.pow (ENNReal.tendsto_ofReal hlim)
      · left; simp
    rw [ENNReal.ofReal_one, one_pow, one_mul] at ht
    exact le_of_tendsto' ht hb
  -- average cost
  intro θ i
  have hst := fun v => dso_stat_eq M hA f (αs v) (hαs v)
  have hsub : ∀ v j a, discCost f.toPolicy (αs v) j ≤ (M.C j a : ℝ≥0∞) +
      ENNReal.ofReal (αs v) * ∑ k, M.P j a k * discCost f.toPolicy (αs v) k := by
    intro v
    obtain ⟨f', V', -, hb', hlo, hup⟩ := dso_main M hA (αs v) (hαs v)
    have hV : V' = fun j => discCost f.toPolicy (αs v) j := funext fun j =>
      le_antisymm (hlo _ j) ((hopt v f'.toPolicy j).trans (hup j))
    subst hV
    exact hb'
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℕ → S → ℝ, (∀ v j, 0 ≤ x v j) ∧
      ∀ v j, discCost f.toPolicy (αs v) j = ENNReal.ofReal (x v j) :=
    ⟨fun v j => (discCost f.toPolicy (αs v) j).toReal, fun _ _ => ENNReal.toReal_nonneg,
      fun v j => (ENNReal.ofReal_toReal ((hst v).1 j)).symm⟩
  have hxe : ∀ v j, x v j = (M.C j (f.f j) : ℝ) + αs v * ∑ k, dpr M j (f.f j) k * x v k := by
    intro v j
    have h := (hst v).2 j
    simp only [hx] at h
    rw [dso_G_eq M _ (hαs v).1.le _ (hx0 v)] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (hx0 v j)
      (dso_rhs_nonneg M _ (hαs v).1.le _ (hx0 v) j _)).1 h
  have hxs : ∀ v j a, x v j ≤ (M.C j a : ℝ) + αs v * ∑ k, dpr M j a k * x v k := by
    intro v j a
    have h := hsub v j a
    simp only [hx] at h
    rw [dso_G_eq M _ (hαs v).1.le _ (hx0 v)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (dso_rhs_nonneg M _ (hαs v).1.le _ (hx0 v) j _)).1 h
  set Cmax : ℝ := ∑ j, ∑ a, (M.C j a : ℝ) with hCmax
  have hC : ∀ j a, (M.C j a : ℝ) ≤ Cmax := by
    intro j a
    calc (M.C j a : ℝ) ≤ ∑ a, (M.C j a : ℝ) :=
          Finset.single_le_sum (f := fun a => (M.C j a : ℝ)) (fun _ _ => NNReal.coe_nonneg _)
            (Finset.mem_univ a)
      _ ≤ Cmax := Finset.single_le_sum (f := fun j => ∑ a, (M.C j a : ℝ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ j)
  set u : ℕ → S → ℝ := fun v j => (1 - αs v) * x v j with hu
  have hu0 : ∀ v j, 0 ≤ u v j := fun v j =>
    mul_nonneg (by linarith [(hαs v).2]) (hx0 v j)
  have hpu : ∀ v j a, ∑ k, dpr M j a k * u v k = (1 - αs v) * ∑ k, dpr M j a k * x v k := by
    intro v j a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [hu]; ring
  have huC : ∀ v j, u v j ≤ Cmax := by
    intro v j
    obtain ⟨j0, hj0⟩ := Finite.exists_max (x v)
    have h1 : ∑ k, dpr M j0 (f.f j0) k * x v k ≤ x v j0 := by
      calc ∑ k, dpr M j0 (f.f j0) k * x v k ≤ ∑ k, dpr M j0 (f.f j0) k * x v j0 :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (hj0 k) (dso_pr_nonneg M _ _ k)
        _ = x v j0 := by rw [← Finset.sum_mul, dso_pr_sum, one_mul]
    have h2 := hxe v j0
    have h3 := hC j0 (f.f j0)
    have hα := hαs v
    have h6 := mul_le_mul_of_nonneg_left h1 hα.1.le
    have h4 : (1 - αs v) * x v j0 ≤ Cmax := by nlinarith
    have h5 : (1 - αs v) * x v j ≤ (1 - αs v) * x v j0 :=
      mul_le_mul_of_nonneg_left (hj0 j) (by linarith [hα.2])
    simp only [hu]
    linarith
  have hue : ∀ v j, u v j = (1 - αs v) * (M.C j (f.f j) : ℝ) +
      αs v * ∑ k, dpr M j (f.f j) k * u v k := by
    intro v j
    rw [hpu]
    have := hxe v j
    simp only [hu]
    rw [this]
    ring
  have hus : ∀ v j a, u v j ≤ (1 - αs v) * (M.C j a : ℝ) +
      αs v * ∑ k, dpr M j a k * u v k := by
    intro v j a
    rw [hpu]
    have := mul_le_mul_of_nonneg_left (hxs v j a) (show 0 ≤ 1 - αs v by linarith [(hαs v).2])
    simp only [hu]
    nlinarith
  have hmem : ∀ v, u v ∈ Set.Icc (0 : S → ℝ) (fun _ => Cmax) :=
    fun v => ⟨fun j => hu0 v j, fun j => huC v j⟩
  obtain ⟨g, hgmem, φ, hφ, hgt⟩ := isCompact_Icc.tendsto_subseq hmem
  have hg0 : ∀ j, 0 ≤ g j := fun j => hgmem.1 j
  have hut : ∀ j, Filter.Tendsto (fun k => u (φ k) j) Filter.atTop (nhds (g j)) :=
    fun j => tendsto_pi_nhds.1 hgt j
  have hαt : Filter.Tendsto (fun k => αs (φ k)) Filter.atTop (nhds 1) :=
    hlim.comp hφ.tendsto_atTop
  have hlimR : ∀ j a, Filter.Tendsto (fun k => (1 - αs (φ k)) * (M.C j a : ℝ) +
      αs (φ k) * ∑ k', dpr M j a k' * u (φ k) k') Filter.atTop
      (nhds (∑ k', dpr M j a k' * g k')) := by
    intro j a
    have := (((tendsto_const_nhds (x := (1:ℝ))).sub hαt).mul
      (tendsto_const_nhds (x := (M.C j a : ℝ)))).add
      (hαt.mul (tendsto_finset_sum Finset.univ fun k' _ =>
        (tendsto_const_nhds (x := dpr M j a k')).mul (hut k')))
    simpa using this
  have hgh : ∀ j, g j = ∑ k, dpr M j (f.f j) k * g k := fun j =>
    tendsto_nhds_unique (hut j) ((hlimR j (f.f j)).congr fun k => (hue (φ k) j).symm)
  have hgs : ∀ j a, g j ≤ ∑ k, dpr M j a k * g k := fun j a =>
    le_of_tendsto_of_tendsto' (hut j) (hlimR j a) fun k => hus (φ k) j a
  set d : ℕ → ℝ := fun k => ∑ j, |u (φ k) j - g j| with hd
  have hdj : ∀ k j, |u (φ k) j - g j| ≤ d k := fun k j =>
    Finset.single_le_sum (f := fun j => |u (φ k) j - g j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  have hdn : ∀ k, 0 ≤ d k := fun k => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hd0 : Filter.Tendsto d Filter.atTop (nhds 0) := by
    have := tendsto_finset_sum Finset.univ fun j _ => ((hut j).sub_const (g j)).abs
    simpa using this
  -- f side
  have hfk : ∀ k, avgCost f.toPolicy i ≤ ENNReal.ofReal (g i + d k) := by
    intro k
    set v := φ k
    let V : S → ℝ≥0∞ := fun j => ENNReal.ofReal (x v j)
    let U : S → ℝ≥0∞ := fun j => ENNReal.ofReal (u v j)
    let W : S → ℝ≥0∞ := fun j => ENNReal.ofReal (g j + d k)
    have hE : ∀ j, (M.C j (f.f j) : ℝ≥0∞) + ∑ k', M.P j (f.f j) k' * V k' ≤
        V j + ∑ k', M.P j (f.f j) k' * U k' := by
      intro j
      simp only [V, U]
      rw [dso_sumP M _ _ _ (hx0 v), dso_sumP M _ _ _ (hu0 v), ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_add (NNReal.coe_nonneg _) (dso_psum_nonneg M _ (hx0 v) _ _),
        ← ENNReal.ofReal_add (hx0 v j) (dso_psum_nonneg M _ (hu0 v) _ _)]
      apply ENNReal.ofReal_le_ofReal
      rw [hpu]
      have := hxe v j
      nlinarith
    have htele := dso_tele_ge hA f.toPolicy i V U
      (dso_stat_w2 f _ _ hE)
    have hWh : ∀ j, W j = ∑ k', M.P j (f.f j) k' * W k' := by
      intro j
      simp only [W]
      rw [dso_sumP M _ _ _ (fun j => add_nonneg (hg0 j) (hdn k))]
      congr 1
      rw [show ∑ k', dpr M j (f.f j) k' * (g k' + d k) = ∑ k', dpr M j (f.f j) k' * g k' +
        (∑ k', dpr M j (f.f j) k') * d k by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]; congr 1; ext k'; ring,
        dso_pr_sum, one_mul, ← hgh j]
    have hUW : ∀ t, dPhi f.toPolicy i (t + 1) U ≤ W i := by
      intro t
      calc dPhi f.toPolicy i (t + 1) U ≤ dPhi f.toPolicy i (t + 1) W :=
            dso_phi_mono hA _ _ _ _ _ fun j => by
              apply ENNReal.ofReal_le_ofReal
              have := hdj k j
              rw [abs_le] at this
              linarith
        _ = W i := dso_harm hA _ _ _
            (dso_stat_w3 f (fun j _ => W j) (fun j a => ∑ k', M.P j a k' * W k') hWh) _
    have hs : ∀ n : ℕ, horizonCost f.toPolicy n i ≤ V i + n * W i := by
      intro n
      calc horizonCost f.toPolicy n i ≤ horizonCost f.toPolicy n i + dPhi f.toPolicy i n V :=
            le_self_add
        _ ≤ V i + ∑ t ∈ Finset.range n, dPhi f.toPolicy i (t + 1) U := htele n
        _ ≤ V i + ∑ t ∈ Finset.range n, W i := by gcongr with t _; exact hUW t
        _ = V i + n * W i := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact dso_avg_le _ _ _ ENNReal.ofReal_ne_top hs
  -- θ side
  have hθk : ∀ k, ENNReal.ofReal (max (g i - d k) 0) ≤ avgCost θ i := by
    intro k
    set v := φ k
    let V : S → ℝ≥0∞ := fun j => ENNReal.ofReal (x v j)
    let U : S → ℝ≥0∞ := fun j => ENNReal.ofReal (u v j)
    let Y : S → ℝ≥0∞ := fun j => ENNReal.ofReal (max (g j - d k) 0)
    have hE : ∀ j a, V j + ∑ k', M.P j a k' * U k' ≤
        (M.C j a : ℝ≥0∞) + ∑ k', M.P j a k' * V k' := by
      intro j a
      simp only [V, U]
      rw [dso_sumP M _ _ _ (hx0 v), dso_sumP M _ _ _ (hu0 v), ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_add (NNReal.coe_nonneg _) (dso_psum_nonneg M _ (hx0 v) _ _),
        ← ENNReal.ofReal_add (hx0 v j) (dso_psum_nonneg M _ (hu0 v) _ _)]
      apply ENNReal.ofReal_le_ofReal
      rw [hpu]
      have := hxs v j a
      nlinarith
    have htele := dso_tele_le hA θ i V U (fun r j a => mul_le_mul_of_nonneg_left (hE j a) bot_le)
    set B : ℝ≥0∞ := ∑ j, V j
    have hBt : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
    have hPB : ∀ n, dPhi θ i n V ≤ B := by
      intro n
      calc dPhi θ i n V ≤ dPhi θ i n (fun _ => B) :=
            dso_phi_mono hA _ _ _ _ _ fun j =>
              Finset.single_le_sum (f := V) (fun _ _ => bot_le) (Finset.mem_univ j)
        _ = B := dso_phi_const hA _ _ _ _
    have hYsub : ∀ j a, Y j ≤ ∑ k', M.P j a k' * Y k' := by
      intro j a
      simp only [Y]
      rw [dso_sumP M _ _ _ (fun j => le_max_right _ _)]
      apply ENNReal.ofReal_le_ofReal
      apply max_le
      · have h1 : ∑ k', dpr M j a k' * (g k' - d k) = ∑ k', dpr M j a k' * g k' - d k := by
          rw [show ∑ k', dpr M j a k' * (g k' - d k) = ∑ k', dpr M j a k' * g k' -
            (∑ k', dpr M j a k') * d k by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext k'; ring,
            dso_pr_sum, one_mul]
        have h2 : ∑ k', dpr M j a k' * (g k' - d k) ≤ ∑ k', dpr M j a k' * max (g k' - d k) 0 :=
          Finset.sum_le_sum fun k' _ =>
            mul_le_mul_of_nonneg_left (le_max_left _ _) (dso_pr_nonneg M _ _ _)
        linarith [hgs j a]
      · exact dso_psum_nonneg M _ (fun j => le_max_right _ _) _ _
    have hYU : ∀ t, Y i ≤ dPhi θ i (t + 1) U := by
      intro t
      calc Y i ≤ dPhi θ i (t + 1) Y := dso_subharm hA θ i Y hYsub _
        _ ≤ dPhi θ i (t + 1) U := dso_phi_mono hA _ _ _ _ _ fun j => by
            apply ENNReal.ofReal_le_ofReal
            have := hdj k j
            rw [abs_le] at this
            exact max_le (by linarith) (hu0 v j)
    have hs : ∀ n : ℕ, n * Y i ≤ horizonCost θ n i + B := by
      intro n
      calc (n : ℝ≥0∞) * Y i = ∑ t ∈ Finset.range n, Y i := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U := by gcongr with t _; exact hYU t
        _ ≤ V i + ∑ t ∈ Finset.range n, dPhi θ i (t + 1) U := le_add_self
        _ ≤ horizonCost θ n i + dPhi θ i n V := htele n
        _ ≤ horizonCost θ n i + B := by gcongr; exact hPB n
    exact dso_avg_ge _ _ _ hBt hs
  have h1 : avgCost f.toPolicy i ≤ ENNReal.ofReal (g i) := by
    have ht : Filter.Tendsto (fun k => ENNReal.ofReal (g i + d k)) Filter.atTop
        (nhds (ENNReal.ofReal (g i + 0))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.add hd0)
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hfk
  have h2 : ENNReal.ofReal (g i) ≤ avgCost θ i := by
    have ht : Filter.Tendsto (fun k => ENNReal.ofReal (max (g i - d k) 0)) Filter.atTop
        (nhds (ENNReal.ofReal (max (g i - 0) 0))) :=
      ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub hd0).max tendsto_const_nhds)
    rw [sub_zero, max_eq_left (hg0 i)] at ht
    exact le_of_tendsto' ht hθk
  exact h1.trans h2

end

end DermanSeqDecisions.Stationary

open DermanSeqDecisions.Stationary


theorem solution {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ((∀ i a, 0 < M.C i a) →
      ∃ R₁ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        avgCost R₁.toPolicy i ≤ avgCost θ i) ∧
    (∀ L : S, (∀ a, M.P L a L = 1) → (∀ a, M.C L a = 0) → (∀ i a, i ≠ L → 0 < M.C i a) →
      ∃ R₂ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        totalCost R₂.toPolicy i ≤ totalCost θ i) := by
  obtain ⟨f, h1, h2⟩ := t1_core M hA; exact ⟨fun _ => ⟨f, h1⟩, fun _ _ _ _ => ⟨f, h2⟩⟩
