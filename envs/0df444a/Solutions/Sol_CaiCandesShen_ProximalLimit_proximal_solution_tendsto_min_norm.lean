-- Prove2me | solution 1 for CaiCandesShen.ProximalLimit.proximal_solution_tendsto_min_norm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:00:08.868458+00:00
-- url     : https://prove2.me/submissions/feff7dc9-e139-42dc-987d-fb8bf6421681

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology


namespace CaiCandesShen.ProximalLimit

open Module
open scoped InnerProductSpace

section auxPLS

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The sum of singular values equals `∑ ‖T bᵢ‖` for the eigenbasis of `T* T`. -/
lemma aux_pls_sum_sv (T : E →ₗ[ℝ] F) :
    (T.singularValues.sum fun _ s => s) =
      ∑ i, ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ := by
  have h1 : (T.singularValues.sum fun _ s => s) =
      ∑ i : Fin (finrank ℝ E), √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i) := by
    unfold LinearMap.singularValues
    rw [Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (by simp)]
    simp [Finsupp.ofSupportFinite_coe]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ ^ 2 =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
      LinearMap.IsSymmetric.apply_eigenvectorBasis]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq,
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal.1 i]
    simp
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

lemma aux_pls_normsq {ι : Type*} [Fintype ι] (w : ι → F) (hw1 : ∀ i, ‖w i‖ ≤ 1)
    (hw2 : Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) (a : ι → ℝ) :
    ‖∑ i, a i • w i‖ ^ 2 ≤ ∑ i, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h1 := hw1 i
    have h2 := norm_nonneg (w i)
    have h3 : 0 ≤ a i ^ 2 * (1 - ‖w i‖ ^ 2) := mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith
  · intro k _ hki
    rw [real_inner_smul_left, real_inner_smul_right, hw2 (Ne.symm hki)]
    ring
  · simp

/-- A von Neumann type trace inequality. -/
lemma aux_pls_vn {ι κ : Type*} [Fintype ι] [Fintype κ] (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (w : ι → F)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hw2 : Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) :
    ∑ i, ⟪T (b i), w i⟫_ℝ ≤ ∑ j, ‖T (c j)‖ := by
  have h1 : ∀ i, ⟪T (b i), w i⟫_ℝ = ∑ j, ⟪c j, b i⟫_ℝ * ⟪T (c j), w i⟫_ℝ := by
    intro i
    conv_lhs => rw [← c.sum_repr' (b i)]
    rw [map_sum, sum_inner]
    simp [real_inner_smul_left]
  have h2 : ∀ j, ∑ i, ⟪c j, b i⟫_ℝ * ⟪T (c j), w i⟫_ℝ =
      ⟪T (c j), ∑ i, ⟪c j, b i⟫_ℝ • w i⟫_ℝ := by
    intro j
    rw [inner_sum]
    simp [real_inner_smul_right]
  have h3 : ∀ j, ‖∑ i, ⟪c j, b i⟫_ℝ • w i‖ ≤ 1 := by
    intro j
    have h4 := aux_pls_normsq w hw1 hw2 (fun i => ⟪c j, b i⟫_ℝ)
    have hs : ∑ i, ⟪c j, b i⟫_ℝ ^ 2 = 1 := by
      have := b.sum_inner_mul_inner (c j) (c j)
      rw [real_inner_self_eq_norm_sq, c.orthonormal.1 j] at this
      simpa [sq, real_inner_comm] using this
    have hn := norm_nonneg (∑ i, ⟪c j, b i⟫_ℝ • w i)
    rw [hs] at h4
    nlinarith
  calc ∑ i, ⟪T (b i), w i⟫_ℝ = ∑ i, ∑ j, ⟪c j, b i⟫_ℝ * ⟪T (c j), w i⟫_ℝ :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ j, ∑ i, ⟪c j, b i⟫_ℝ * ⟪T (c j), w i⟫_ℝ := Finset.sum_comm
    _ = ∑ j, ⟪T (c j), ∑ i, ⟪c j, b i⟫_ℝ • w i⟫_ℝ := Finset.sum_congr rfl fun j _ => h2 j
    _ ≤ ∑ j, ‖T (c j)‖ := Finset.sum_le_sum fun j _ => by
        calc _ ≤ ‖T (c j)‖ * ‖∑ i, ⟪c j, b i⟫_ℝ • w i‖ := real_inner_le_norm _ _
          _ ≤ ‖T (c j)‖ * 1 := mul_le_mul_of_nonneg_left (h3 j) (norm_nonneg _)
          _ = _ := mul_one _

lemma aux_pls_attain (T : E →ₗ[ℝ] F) :
    ∃ w : Fin (finrank ℝ E) → F, (∀ i, ‖w i‖ ≤ 1) ∧ (Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) ∧
      ∑ i, ⟪T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i), w i⟫_ℝ =
        (T.singularValues.sum fun _ s => s) := by
  set hT := T.isSymmetric_adjoint_comp_self
  set b := hT.eigenvectorBasis rfl with hb
  refine ⟨fun i => ‖T (b i)‖⁻¹ • T (b i), ?_, ?_, ?_⟩
  · intro i
    rcases eq_or_ne ‖T (b i)‖ 0 with h | h
    · simp [h]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
  · intro i j hij
    simp only
    rw [real_inner_smul_left, real_inner_smul_right]
    have : ⟪T (b i), T (b j)⟫_ℝ = 0 := by
      rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hb,
        LinearMap.IsSymmetric.apply_eigenvectorBasis, real_inner_smul_right,
        (hT.eigenvectorBasis rfl).orthonormal.2 hij, mul_zero]
    rw [this]
    ring
  · rw [aux_pls_sum_sv]
    show ∑ i, ⟪T (b i), ‖T (b i)‖⁻¹ • T (b i)⟫_ℝ = ∑ i, ‖T (b i)‖
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖T (b i)‖ 0 with h | h
    · simp [h]
    · field_simp

end auxPLS

section auxMat

variable {n₁ n₂ : ℕ}

lemma aux_pls_nn_le {ι : Type*} [Fintype ι] (X : Mat n₁ n₂)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin n₂))) (w : ι → EuclideanSpace ℝ (Fin n₁))
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hw2 : Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) :
    ∑ i, ⟪Matrix.toEuclideanLin X (b i), w i⟫_ℝ ≤ nuclearNorm X := by
  unfold nuclearNorm
  rw [aux_pls_sum_sv]
  exact aux_pls_vn _ b _ w hw1 hw2

lemma aux_pls_nn_attain (X : Mat n₁ n₂) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℝ (EuclideanSpace ℝ (Fin n₂)))) ℝ
        (EuclideanSpace ℝ (Fin n₂))) (w : Fin (finrank ℝ (EuclideanSpace ℝ (Fin n₂))) →
          EuclideanSpace ℝ (Fin n₁)),
      (∀ i, ‖w i‖ ≤ 1) ∧ (Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) ∧
      ∑ i, ⟪Matrix.toEuclideanLin X (b i), w i⟫_ℝ = nuclearNorm X := by
  obtain ⟨w, h1, h2, h3⟩ := aux_pls_attain (Matrix.toEuclideanLin X)
  exact ⟨_, w, h1, h2, h3⟩

lemma aux_pls_nn_convex (X Y : Mat n₁ n₂) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    nuclearNorm (a • X + c • Y) ≤ a * nuclearNorm X + c * nuclearNorm Y := by
  obtain ⟨b, w, h1, h2, h3⟩ := aux_pls_nn_attain (a • X + c • Y)
  rw [← h3]
  have hX := aux_pls_nn_le X b w h1 h2
  have hY := aux_pls_nn_le Y b w h1 h2
  have : ∑ i, ⟪Matrix.toEuclideanLin (a • X + c • Y) (b i), w i⟫_ℝ =
      a * ∑ i, ⟪Matrix.toEuclideanLin X (b i), w i⟫_ℝ +
        c * ∑ i, ⟪Matrix.toEuclideanLin Y (b i), w i⟫_ℝ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hX ha, mul_le_mul_of_nonneg_left hY hc]

lemma aux_pls_cont_L {ι : Type*} [Fintype ι]
    (b : ι → EuclideanSpace ℝ (Fin n₂)) (w : ι → EuclideanSpace ℝ (Fin n₁)) :
    Continuous (fun X : Mat n₁ n₂ => ∑ i, ⟪Matrix.toEuclideanLin X (b i), w i⟫_ℝ) := by
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous (LinearMap.applyₗ (R := ℝ) (b i) ∘ₗ
      (Matrix.toEuclideanLin (m := Fin n₁) (n := Fin n₂) (𝕜 := ℝ)).toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  exact hc.inner continuous_const

lemma aux_pls_frob_sq (X : Mat n₁ n₂) : frobNorm X ^ 2 = frobInner X X := by
  unfold frobNorm
  rw [Real.sq_sqrt]
  unfold frobInner
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

lemma aux_pls_frob_cont : Continuous (fun X : Mat n₁ n₂ => frobNorm X ^ 2) := by
  have : (fun X : Mat n₁ n₂ => frobNorm X ^ 2) = fun X => ∑ i, ∑ j, X i j * X i j := by
    funext X
    rw [aux_pls_frob_sq]
    rfl
  rw [this]
  fun_prop

lemma aux_pls_unique {m : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (Xinf : Mat n₁ n₂)
    (hXinf : IsMinFrobeniusSolution f Xinf) (Y : Mat n₁ n₂)
    (hY : IsNuclearNormSolution f Y) (hYF : frobNorm Y ^ 2 ≤ frobNorm Xinf ^ 2) :
    Y = Xinf := by
  set M : Mat n₁ n₂ := (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Xinf with hM
  have hMfeas : Feasible f M := by
    intro i
    have := (hconv i).2 (Set.mem_univ Y) (Set.mem_univ Xinf) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h1 := hY.1 i
    have h2 := hXinf.1.1 i
    simp only [smul_eq_mul] at this
    rw [hM]
    linarith
  have hMnuc : IsNuclearNormSolution f M := by
    refine ⟨hMfeas, fun X' hX' => ?_⟩
    have h1 := aux_pls_nn_convex Y Xinf (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 := hY.2 X' hX'
    have h3 := hXinf.1.2 X' hX'
    rw [hM]
    linarith
  have hMF := hXinf.2 M hMnuc
  rw [aux_pls_frob_sq, aux_pls_frob_sq] at hMF hYF
  have hid : 2 * frobInner Y Y + 2 * frobInner Xinf Xinf - 4 * frobInner M M =
      ∑ i, ∑ j, (Y i j - Xinf i j) ^ 2 := by
    simp only [frobInner, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hle : ∑ i, ∑ j, (Y i j - Xinf i j) ^ 2 ≤ 0 := by
    rw [← hid]; linarith
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, (Y i j - Xinf i j) ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h0 : ∑ i, ∑ j, (Y i j - Xinf i j) ^ 2 = 0 :=
    le_antisymm hle (Finset.sum_nonneg hnn)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  ext i j
  have h0i := h0 i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at h0i
  have := h0i j (Finset.mem_univ _)
  nlinarith [sq_nonneg (Y i j - Xinf i j)]

end auxMat

theorem aux_sle {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ))
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (Xc : Mat n₁ n₂)
    (hXc : Tendsto (fun k => Xτ (t k)) atTop (𝓝 Xc)) :
    Xc = Xinf := by
  have hpos : ∀ᶠ k in atTop, 0 < t k := ht.eventually_gt_atTop 0
  have hfeas_k : ∀ᶠ k in atTop, Feasible f (Xτ (t k)) :=
    hpos.mono fun k hk => (hXτ _ hk).1
  -- the limit is feasible
  have hfeas : Feasible f Xc := by
    intro i
    by_contra h
    push Not at h
    have h1 := (hlsc i Xc) 0 h
    have h2 := hXc.eventually h1
    obtain ⟨k, hk1, hk2⟩ := (h2.and hfeas_k).exists
    linarith [hk2 i]
  -- comparison with `Xinf`
  have hkey : ∀ᶠ k in atTop, frobNorm (Xτ (t k)) ^ 2 ≤ frobNorm Xinf ^ 2 ∧
      nuclearNorm (Xτ (t k)) ≤ nuclearNorm Xinf + frobNorm Xinf ^ 2 / (2 * t k) := by
    filter_upwards [hpos] with k hk
    have h1 := (hXτ _ hk).2 Xinf hXinf.1.1
    have h2 := hXinf.1.2 _ (hXτ _ hk).1
    unfold fτ at h1
    have hF := sq_nonneg (frobNorm (Xτ (t k)))
    have hp : 0 ≤ t k * (nuclearNorm (Xτ (t k)) - nuclearNorm Xinf) :=
      mul_nonneg hk.le (sub_nonneg.2 h2)
    constructor
    · nlinarith
    · rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
      nlinarith
  -- Frobenius bound passes to the limit
  have hFc : frobNorm Xc ^ 2 ≤ frobNorm Xinf ^ 2 :=
    le_of_tendsto ((aux_pls_frob_cont.tendsto Xc).comp hXc) (hkey.mono fun k hk => hk.1)
  -- nuclear norm bound passes to the limit
  have hNc : nuclearNorm Xc ≤ nuclearNorm Xinf := by
    obtain ⟨b, w, h1, h2, h3⟩ := aux_pls_nn_attain Xc
    rw [← h3]
    have hL := ((aux_pls_cont_L (n₁ := n₁) (n₂ := n₂) b w).tendsto Xc).comp hXc
    have hR : Tendsto (fun k => nuclearNorm Xinf + frobNorm Xinf ^ 2 / (2 * t k)) atTop
        (𝓝 (nuclearNorm Xinf + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (ht.const_mul_atTop two_pos))
    rw [add_zero] at hR
    refine le_of_tendsto_of_tendsto hL hR (hkey.mono fun k hk => ?_)
    exact (aux_pls_nn_le _ b w h1 h2).trans hk.2
  have hnuc : IsNuclearNormSolution f Xc :=
    ⟨hfeas, fun X' hX' => hNc.trans (hXinf.1.2 X' hX')⟩
  exact aux_pls_unique f hconv Xinf hXinf Xc hnuc hFc

lemma aux_entry_bound {n₁ n₂ : ℕ} (X : Mat n₁ n₂) (c : ℝ) (h : frobInner X X ≤ c) (i : Fin n₁)
    (j : Fin n₂) : X i j ∈ Set.Icc (-(c + 1)) (c + 1) := by
  have h1 : X i j * X i j ≤ frobInner X X := by
    unfold frobInner
    have hi : ∑ j', X i j' * X i j' ≤ ∑ i', ∑ j', X i' j' * X i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', X i' j' * X i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => mul_self_nonneg _) (Finset.mem_univ i)
    have hj : X i j * X i j ≤ ∑ j', X i j' * X i j' :=
      Finset.single_le_sum (f := fun j' => X i j' * X i j')
        (fun j' _ => mul_self_nonneg _) (Finset.mem_univ j)
    linarith
  have hc : 0 ≤ c := le_trans (mul_self_nonneg _) (h1.trans h)
  constructor <;> nlinarith

theorem goal_core {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => frobNorm (Xτ τ - Xinf)) atTop (𝓝 0) := by
  set c := frobNorm Xinf ^ 2 with hc
  set K : Set (Mat n₁ n₂) := Set.pi Set.univ (fun _ => Set.pi Set.univ
    (fun _ => Set.Icc (-(c + 1)) (c + 1))) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hbound : ∀ τ, 0 < τ → Xτ τ ∈ K := by
    intro τ hτ
    obtain ⟨hfeas, hmin⟩ := hXτ τ hτ
    have h1 : fτ τ (Xτ τ) ≤ fτ τ Xinf := hmin Xinf hXinf.1.1
    have h2 : nuclearNorm Xinf ≤ nuclearNorm (Xτ τ) := hXinf.1.2 (Xτ τ) hfeas
    have h3 : τ * nuclearNorm Xinf ≤ τ * nuclearNorm (Xτ τ) :=
      mul_le_mul_of_nonneg_left h2 hτ.le
    unfold fτ at h1
    have h4 : frobNorm (Xτ τ) ^ 2 ≤ c := by rw [hc]; linarith
    rw [aux_pls_frob_sq] at h4
    intro i _ j _
    exact aux_entry_bound _ c h4 i j
  haveI : SecondCountableTopology (Mat n₁ n₂) :=
    inferInstanceAs (SecondCountableTopology (Fin n₁ → Fin n₂ → ℝ))
  have hT : Tendsto Xτ atTop (𝓝 Xinf) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have hfreq : ∃ᶠ k in atTop, Xτ (ns k) ∈ K :=
      ((hns.eventually_gt_atTop 0).mono fun k hk => hbound _ hk).frequently
    obtain ⟨a, _, φ, hφ, hlim⟩ := hKc.tendsto_subseq' hfreq
    refine ⟨φ, ?_⟩
    have ht : Tendsto (ns ∘ φ) atTop atTop := hns.comp hφ.tendsto_atTop
    have := aux_sle f hconv hlsc Xinf hXinf Xτ hXτ (ns ∘ φ) ht a hlim
    subst this
    exact hlim
  have hcont : Continuous (fun X : Mat n₁ n₂ => frobNorm (X - Xinf)) := by
    unfold frobNorm frobInner
    fun_prop
  have := (hcont.tendsto Xinf).comp hT
  simpa [Function.comp_def, frobNorm, frobInner] using this

end CaiCandesShen.ProximalLimit

open CaiCandesShen.ProximalLimit


theorem solution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => frobNorm (Xτ τ - Xinf)) atTop (𝓝 0) := by
  exact goal_core f hconv hlsc Xinf hXinf Xτ hXτ
