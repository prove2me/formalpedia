-- Prove2me | solution 1 for BookProof.FullQuadratic.fqOp_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:04:56.555952+00:00
-- url     : https://prove2.me/submissions/2feb4996-a3bc-47dd-b5cf-cd63811ba825

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStep
import Definitions.Def_ChapterCarlemanSimplex
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_HermiteBand_pgLp_hpsi
import Theorems.Thm_BookProof_HermiteBand_isBand2_fqPoly
import Theorems.Thm_BookProof_FullQuadratic_fqOp_symmetric
-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_deficiencyTrivialAt
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

namespace A3Band

open BookProof.HermiteBand

lemma coreEquiv_val (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv (d := d) p : polyGaussCore (d := d)) : L2d d) = pgLp p :=
  rfl

/-- Multi-indices of total degree `n`. -/
def shell (n : ℕ) : Finset (Fin d →₀ ℕ) := (Finset.univ : Finset (Fin d)).finsuppAntidiag n

lemma mem_shell {n : ℕ} {α : Fin d →₀ ℕ} : α ∈ shell n ↔ α.degree = n := by
  simp [shell, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

/-- Multi-indices whose degree lies in `s`. -/
def blk (s : Finset ℕ) : Finset (Fin d →₀ ℕ) := s.biUnion shell

lemma mem_blk {s : Finset ℕ} {α : Fin d →₀ ℕ} : α ∈ blk s ↔ α.degree ∈ s := by
  simp [blk, mem_shell]

lemma sum_blk (s : Finset ℕ) (g : (Fin d →₀ ℕ) → ℝ) :
    ∑ α ∈ blk s, g α = ∑ n ∈ s, ∑ α ∈ shell n, g α := by
  rw [blk, Finset.sum_biUnion]
  intro m _ n _ hmn
  rw [Function.onFun, Finset.disjoint_left]
  intro α h1 h2
  rw [mem_shell] at h1 h2
  exact hmn (h1.symm.trans h2)

/-- **Carleman flux criterion for band operators**: a symmetric operator on the Gauss–polynomial
core whose Hermite matrix is a second-order band matrix with entries `O(deg + 1)` has trivial
deficiency spaces off the real axis. -/
theorem deficiency_of_band (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (hT : IsBand2 T)
    (hsym : SymmetricOn (polyGaussCore (d := d))
      ((polyGaussCore (d := d)).subtype ∘ₗ coreOp T))
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d))
      ((polyGaussCore (d := d)).subtype ∘ₗ coreOp T) z := by
  obtain ⟨M, C, hC, hb⟩ := hT
  choose f hf hcard hdeg hbound using hb
  set A := (polyGaussCore (d := d)).subtype ∘ₗ coreOp T with hA
  let e : (Fin d →₀ ℕ) → L2d d := hermiteMvLp
  have he : Orthonormal ℂ e := orthonormal_hermiteMvLp
  let ve : (Fin d →₀ ℕ) → polyGaussCore (d := d) :=
    fun α => ⟨hermiteMvLp α, hermiteMvLp_mem_core α⟩
  have hAv : ∀ α, A (ve α) = ∑ β ∈ (f α).support, f α β • e β := by
    intro α
    have h1 : (coreEquiv (d := d)).symm (ve α) = hpsi α := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [coreEquiv_val, pgLp_hpsi]
    simp only [hA, coreOp, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, h1,
      hf]
    rw [coreEquiv_val, ← pgMap_apply, hcomb, Finsupp.apply_linearCombination,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro β _
    simp [pgMap_apply, pgLp_hpsi, e]
  have hcoef : ∀ α β, inner ℂ (e β) (A (ve α)) = f α β := by
    intro α β
    rw [hAv]
    by_cases hβ : β ∈ (f α).support
    · exact he.inner_right_sum (fun γ => f α γ) hβ
    · rw [Finsupp.notMem_support_iff.mp hβ, inner_sum]
      apply Finset.sum_eq_zero
      intro γ hγ
      have hne : β ≠ γ := fun h => hβ (h ▸ hγ)
      rw [inner_smul_right, orthonormal_iff_ite.mp he β γ, if_neg hne, mul_zero]
  have hsymf : ∀ α β, f α β = (starRingEnd ℂ) (f β α) := by
    intro α β
    have h := hsym (ve β) (ve α)
    rw [← hcoef α β, ← hcoef β α, inner_conj_symm]
    exact h.symm
  have hzero : ∀ α β, f α β ≠ 0 → β.degree ≤ α.degree + 2 ∧ α.degree ≤ β.degree + 2 := by
    intro α β h
    have := hdeg α β (Finsupp.mem_support_iff.mpr h)
    omega
  have hrow : ∀ α (V : Finset (Fin d →₀ ℕ)),
      ∑ β ∈ V, ‖f α β‖ ≤ M * (C * (α.degree + 1)) := by
    intro α V
    calc ∑ β ∈ V, ‖f α β‖ ≤ ∑ β ∈ V ∪ (f α).support, ‖f α β‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun _ _ _ => norm_nonneg _)
      _ = ∑ β ∈ (f α).support, ‖f α β‖ :=
          (Finset.sum_subset Finset.subset_union_right
            (fun β _ hβ => by rw [Finsupp.notMem_support_iff.mp hβ, norm_zero])).symm
      _ ≤ ∑ β ∈ (f α).support, C * (α.degree + 1) := by
          apply Finset.sum_le_sum; intro β _
          have := hbound α β
          simpa [g2] using this
      _ = (f α).support.card * (C * (α.degree + 1)) := by simp
      _ ≤ M * (C * (α.degree + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard α
  have hcol : ∀ β (V : Finset (Fin d →₀ ℕ)),
      ∑ α ∈ V, ‖f α β‖ ≤ M * (C * (β.degree + 1)) := by
    intro β V
    calc ∑ α ∈ V, ‖f α β‖ = ∑ α ∈ V, ‖f β α‖ := by
          apply Finset.sum_congr rfl; intro α _; rw [hsymf α β, Complex.norm_conj]
      _ ≤ _ := hrow β V
  intro w hw
  obtain ⟨c, hc⟩ : ∃ c : (Fin d →₀ ℕ) → ℂ, c = fun α => inner ℂ (e α) w := ⟨_, rfl⟩
  have heig : ∀ α (U : Finset (Fin d →₀ ℕ)), (f α).support ⊆ U →
      ∑ β ∈ U, (starRingEnd ℂ) (f α β) * c β = z * c α := by
    intro α U hU
    have h := hw (ve α)
    rw [hAv, sum_inner] at h
    simp only [inner_smul_left] at h
    rw [← Finset.sum_subset hU (fun β _ hβ => by rw [Finsupp.notMem_support_iff.mp hβ]; simp), hc]
    exact h
  have hflux : ∀ N : ℕ, |z.im| * ∑ α ∈ blk (range (N + 1)), ‖c α‖ ^ 2 ≤
      (M * (C * ((N : ℝ) + 3))) * ∑ α ∈ blk (Icc (N - 1) (N + 2)), ‖c α‖ ^ 2 := by
    intro N
    set F := blk (d := d) (range (N + 1)) with hFdef
    set U := blk (d := d) (range (N + 3)) with hUdef
    set R := blk (d := d) (Icc (N - 1) (N + 2)) with hRdef
    set K : ℝ := M * (C * ((N : ℝ) + 3)) with hK
    have hK0 : 0 ≤ K := by positivity
    have hFU : F ⊆ U := fun α h => by rw [mem_blk, Finset.mem_range] at h ⊢; omega
    have hsuppU : ∀ α ∈ F, (f α).support ⊆ U := by
      intro α hα β hβ
      rw [mem_blk, mem_range] at hα ⊢
      have := hzero α β (Finsupp.mem_support_iff.mp hβ)
      omega
    have hid : z * (((∑ α ∈ F, ‖c α‖ ^ 2 : ℝ)) : ℂ) =
        ∑ α ∈ F, ∑ β ∈ F, (starRingEnd ℂ) (c α) * ((starRingEnd ℂ) (f α β) * c β) +
        ∑ α ∈ F, ∑ β ∈ U \ F, (starRingEnd ℂ) (c α) * ((starRingEnd ℂ) (f α β) * c β) := by
      rw [← Finset.sum_add_distrib]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α hα
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, add_comm, Finset.sum_sdiff hFU,
        heig α U (hsuppU α hα), ← Complex.conj_mul']
      ring
    have hI : (∑ α ∈ F, ∑ β ∈ F,
        (starRingEnd ℂ) (c α) * ((starRingEnd ℂ) (f α β) * c β)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      simp_rw [map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
      rw [hsymf y x]; ring
    set B := ∑ α ∈ F, ∑ β ∈ U \ F,
        (starRingEnd ℂ) (c α) * ((starRingEnd ℂ) (f α β) * c β) with hBdef
    have hS0 : 0 ≤ ∑ α ∈ F, ‖c α‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hB : z.im * ∑ α ∈ F, ‖c α‖ ^ 2 = B.im := by
      have := congrArg Complex.im hid
      rw [Complex.add_im, hI, zero_add] at this
      rw [← this, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]; ring
    have h1 : |z.im| * ∑ α ∈ F, ‖c α‖ ^ 2 ≤ ‖B‖ := by
      rw [← abs_of_nonneg hS0, ← abs_mul, hB]; exact Complex.abs_im_le_norm B
    -- termwise bound
    have h2 : ‖B‖ ≤ ∑ α ∈ F, ∑ β ∈ U \ F,
        ‖f α β‖ * ((‖c α‖ ^ 2 + ‖c β‖ ^ 2) / 2) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      have := two_mul_le_add_sq ‖c α‖ ‖c β‖
      have := norm_nonneg (f α β)
      nlinarith [mul_le_mul_of_nonneg_left (two_mul_le_add_sq ‖c α‖ ‖c β‖) this]
    have hsplit : ∑ α ∈ F, ∑ β ∈ U \ F, ‖f α β‖ * ((‖c α‖ ^ 2 + ‖c β‖ ^ 2) / 2) =
        (∑ α ∈ F, ‖c α‖ ^ 2 * ∑ β ∈ U \ F, ‖f α β‖) / 2 +
        (∑ β ∈ U \ F, ‖c β‖ ^ 2 * ∑ α ∈ F, ‖f α β‖) / 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm (s := U \ F) (t := F), ← add_div, ← Finset.sum_add_distrib,
        Finset.sum_div]
      apply Finset.sum_congr rfl; intro α _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro β _
      ring
    have hRsub : U \ F ⊆ R := by
      intro β hβ
      rw [Finset.mem_sdiff, mem_blk, mem_blk, mem_range, mem_range] at hβ
      rw [mem_blk, mem_Icc]; omega
    have hT1 : ∑ α ∈ F, ‖c α‖ ^ 2 * ∑ β ∈ U \ F, ‖f α β‖ ≤ K * ∑ α ∈ R, ‖c α‖ ^ 2 := by
      calc ∑ α ∈ F, ‖c α‖ ^ 2 * ∑ β ∈ U \ F, ‖f α β‖
          ≤ ∑ α ∈ F, K * (if α ∈ R then ‖c α‖ ^ 2 else 0) := by
            apply Finset.sum_le_sum; intro α hα
            have hαN : α.degree ≤ N := by rw [mem_blk, mem_range] at hα; omega
            by_cases hR : α ∈ R
            · rw [if_pos hR, mul_comm]
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              refine (hrow α _).trans ?_
              rw [hK]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_left _ hC
              have : (α.degree : ℝ) ≤ N := by exact_mod_cast hαN
              linarith
            · rw [if_neg hR, mul_zero]
              have hz0 : ∑ β ∈ U \ F, ‖f α β‖ = 0 := by
                apply Finset.sum_eq_zero; intro β hβ
                rw [norm_eq_zero]
                by_contra hne
                have := hzero α β hne
                rw [Finset.mem_sdiff, mem_blk, mem_blk, mem_range, mem_range] at hβ
                rw [mem_blk, mem_Icc] at hR
                omega
              rw [hz0, mul_zero]
        _ = K * ∑ α ∈ F ∩ R, ‖c α‖ ^ 2 := by rw [← Finset.mul_sum, Finset.sum_ite_mem]
        _ ≤ K * ∑ α ∈ R, ‖c α‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hK0
            exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun _ _ _ => by positivity)
    have hT2 : ∑ β ∈ U \ F, ‖c β‖ ^ 2 * ∑ α ∈ F, ‖f α β‖ ≤ K * ∑ α ∈ R, ‖c α‖ ^ 2 := by
      calc ∑ β ∈ U \ F, ‖c β‖ ^ 2 * ∑ α ∈ F, ‖f α β‖ ≤ ∑ β ∈ U \ F, K * ‖c β‖ ^ 2 := by
            apply Finset.sum_le_sum; intro β hβ
            have hβN : β.degree ≤ N + 2 := by
              rw [Finset.mem_sdiff, mem_blk, mem_range] at hβ; omega
            rw [mul_comm]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            refine (hcol β _).trans ?_
            rw [hK]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ hC
            have : (β.degree : ℝ) ≤ N + 2 := by exact_mod_cast hβN
            linarith
        _ = K * ∑ β ∈ U \ F, ‖c β‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ K * ∑ α ∈ R, ‖c α‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hK0
            exact Finset.sum_le_sum_of_subset_of_nonneg hRsub (fun _ _ _ => by positivity)
    calc |z.im| * ∑ α ∈ F, ‖c α‖ ^ 2 ≤ ‖B‖ := h1
      _ ≤ _ := h2
      _ = _ := hsplit
      _ ≤ (K * ∑ α ∈ R, ‖c α‖ ^ 2) / 2 + (K * ∑ α ∈ R, ‖c α‖ ^ 2) / 2 := by gcongr
      _ = K * ∑ α ∈ R, ‖c α‖ ^ 2 := by ring
  -- shell masses
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun n => ∑ α ∈ shell n, ‖c α‖ ^ 2 := ⟨_, rfl⟩
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    rw [ha]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hblk : ∀ s : Finset ℕ, ∑ α ∈ blk s, ‖c α‖ ^ 2 = ∑ n ∈ s, a n := fun s => by
    rw [ha]; exact sum_blk s _
  have hasum : Summable a := by
    apply summable_of_sum_range_le ha0 (c := ‖w‖ ^ 2)
    intro L
    rw [← hblk, hc]
    exact he.sum_inner_products_le w
  -- some coefficient is nonzero
  by_contra hw0
  obtain ⟨α0, hα0⟩ : ∃ α, c α ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    have hs := (hermiteMvBasis (d := d)).hasSum_repr w
    have h0 : ∀ i, (hermiteMvBasis (d := d)).repr w i • hermiteMvBasis (d := d) i = 0 := by
      intro i
      rw [HilbertBasis.repr_apply_apply]
      have := h i
      rw [hc] at this
      simp only [hermiteMvBasis, HilbertBasis.coe_mk] at this ⊢
      rw [this, zero_smul]
    simp only [h0] at hs
    exact hs.unique hasSum_zero
  obtain ⟨N0, hN0⟩ : ∃ N0, α0.degree = N0 := ⟨_, rfl⟩
  have hε : 0 < |z.im| * ‖c α0‖ ^ 2 := by positivity
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = M * C := ⟨_, rfl⟩
  have hK0 : 0 ≤ K0 := by rw [hK0def]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, D = fun m => ∑ k ∈ range 4, a (m + k) := ⟨_, rfl⟩
  have hDsum : Summable D := by
    rw [hD]
    apply summable_sum
    intro k _
    exact (summable_nat_add_iff k).mpr hasum
  have hD0 : ∀ m, 0 ≤ D m := fun m => by rw [hD]; exact Finset.sum_nonneg fun _ _ => ha0 _
  have hmain : ∀ m, |z.im| * ‖c α0‖ ^ 2 ≤ K0 * ((m + N0 : ℕ) + 4 : ℝ) * D (m + N0) := by
    intro m
    have h := hflux (m + N0 + 1)
    have hIcc : Icc (m + N0 + 1 - 1) (m + N0 + 1 + 2) = Ico (m + N0) (m + N0 + 4) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hblk, hblk, hIcc, Finset.sum_Ico_eq_sum_range, show m + N0 + 4 - (m + N0) = 4 by omega]
      at h
    have hle : ‖c α0‖ ^ 2 ≤ ∑ n ∈ range (m + N0 + 1 + 1), a n := by
      rw [← hblk]
      apply Finset.single_le_sum (f := fun α => ‖c α‖ ^ 2) (fun _ _ => by positivity)
      rw [mem_blk, mem_range]; omega
    calc |z.im| * ‖c α0‖ ^ 2 ≤ |z.im| * ∑ n ∈ range (m + N0 + 1 + 1), a n := by gcongr
      _ ≤ _ := h
      _ = K0 * ((m + N0 : ℕ) + 4 : ℝ) * D (m + N0) := by
        rw [hK0def, hD]; push_cast; ring
  have hK0pos : 0 < K0 := by
    rcases hK0.lt_or_eq with h | h
    · exact h
    · have := hmain 0
      rw [← h, zero_mul, zero_mul] at this
      linarith
  have hsum2 : Summable (fun m : ℕ => (|z.im| * ‖c α0‖ ^ 2 / K0) *
      (1 / ((m + (N0 + 4) : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_nat_add_iff N0).mpr hDsum)
    have h := hmain m
    have hpos : (0 : ℝ) < ((m + (N0 + 4) : ℕ) : ℝ) := by positivity
    rw [mul_one_div, div_div, div_le_iff₀ (by positivity)]
    have : ((m + (N0 + 4) : ℕ) : ℝ) = ((m + N0 : ℕ) : ℝ) + 4 := by push_cast; ring
    rw [this]
    have hc' := mul_comm (K0 * (((m + N0 : ℕ) : ℝ) + 4)) (D (m + N0))
    linarith
  have hsum3 : Summable (fun m : ℕ => 1 / ((m + (N0 + 4) : ℕ) : ℝ)) :=
    (summable_mul_left_iff (ne_of_gt (by positivity))).mp hsum2
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) (N0 + 4)).mp hsum3)

end A3Band

theorem solution (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (fqOp P Q S b b') z :=
  A3Band.deficiency_of_band (fqPoly P Q S b b') (BookProof.HermiteBand.isBand2_fqPoly P Q S b b')
    (fqOp_symmetric P Q S b b') hz
