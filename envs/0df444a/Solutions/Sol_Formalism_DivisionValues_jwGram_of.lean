-- Prove2me | solution 1 for Formalism.DivisionValues.jwGram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:25:40.453173+00:00
-- url     : https://prove2.me/submissions/9b2aedd6-bbb0-4b4d-9a5c-812645392471

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_eq_dot
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_herm_entry
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_det_ne_zero
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_isSymm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_nondeg
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_det_of_ne_zero
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_gramR_eq_std
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_expand
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_one_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution (hIC : IdxChange) : JwGram := by
  intro K _ _ _ _ K0 hcm d H X hR T hT w f hf
  classical
  have hherm := herm_entry hcm hR
  have hdetH := det_ne_zero hR
  have hs := hform_isSymm H hherm
  have hnd := hform_nondeg H hs hdetH
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨cO K r, rfl⟩
  set h := hform H with hh
  set M : Matrix (Fin d) (Fin d) K := Matrix.of fun a b => h (f a) (f b) with hMdef
  have hM : M.det = gramR H f := by
    unfold gramR
    congr 1
    ext a b
    simp [M, h, hform_eq_dot]
  have hG : gramR H f ≠ 0 := by
    rw [gramR_eq_std]
    have := det_of_ne_zero hf.1
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr this) this) hdetH
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr (hM ▸ hG)
  set fs : Fin d → Fin d → K := fun b => ∑ k, M⁻¹ k b • f k with hfs
  have hpair : ∀ a b, h (f a) (fs b) = if a = b then 1 else 0 := by
    intro a b
    have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
    have := congrFun (congrFun hmul a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, hfs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have hfsli : LinearIndependent K fs := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (h (f i)) hg
    rw [map_sum, map_zero] at this
    simp only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  have hspK : Submodule.span K (Set.range f) = ⊤ :=
    hf.1.span_eq_top_of_card_eq_finrank' (by simp)
  have hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f)) :=
    ⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩
  have hone : ∀ c : K, c ∈ (1 : Submodule (𝓞 K) K) → ∀ r : 𝓞 K,
      star (algebraMap (𝓞 K) K r) * c ∈ (1 : Submodule (𝓞 K) K) := by
    intro c hc r
    exact Formalism.HermitianLatticesTheory.locDual_one_mul (Submodule.mem_one.mpr ⟨cO K r, rfl⟩) hc
  have hdual_span : Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f)) =
      Submodule.span (𝓞 K) (Set.range fs) := by
    apply le_antisymm
    · intro x hx
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
      have hc : ∀ a, h (f a) x ∈ (1 : Submodule (𝓞 K) K) :=
        fun a => hx _ (Submodule.subset_span ⟨a, rfl⟩)
      set b : Basis (Fin d) K (Fin d → K) := Basis.mk hf.1 (by rw [hspK]) with hb
      have hbf : ∀ i, b i = f i := fun i => by simp [b]
      have hexp := Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b fs (by simpa [hbf] using hpair) x
      rw [hexp]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hc j)
      rw [hbf, ← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      change fs b ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [hpair]
        split_ifs
        · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
        · exact Submodule.zero_mem _
      | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left]
        exact hone _ hx r
  have hdualT : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h T) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) h hs hnd hstar T hT).1
  have hLD := Formalism.HermitianLatticesTheory.locDual (𝓞 K) K (Fin d → K) h hs hstar
  have A := (hLD _ hspan_f.fg).1 w.asIdeal w.isPrime
  have B := (hLD _ hT.fg).1 w.asIdeal w.isPrime
  have hlocfs : IsLocBasis (Formalism.HermitianLatticesTheory.dual h T) w fs := by
    refine ⟨hfsli, ?_⟩
    calc Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range fs))
        = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (Set.range f))) := by
          rw [hdual_span]
      _ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal
            (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f))) := by
          rw [A.1, A.2]
      _ = Formalism.HermitianLatticesTheory.dualAt h w.asIdeal (Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal T) := by rw [hf.2]
      _ = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Formalism.HermitianLatticesTheory.dual h T) := by rw [B.1, B.2]
  have hone_f : (fun i => ∑ k, (1 : Matrix (Fin d) (Fin d) K) k i • f k) = f := by
    funext i
    simp [Matrix.one_apply]
  have i1 := (hIC K d T hT f hf.1 w 1 (by rw [hone_f]; exact hf)).1
  have i2 := (hIC K d (Formalism.HermitianLatticesTheory.dual h T) hdualT f hf.1 w M⁻¹ hlocfs).1
  have : w.asIdeal.IsMaximal := w.isMaximal
  have hIB := Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin d → K) h hs hnd hstar w.asIdeal T
    (Submodule.span (𝓞 K) (Set.range f)) (Formalism.HermitianLatticesTheory.dual h T) hT hspan_f hdualT
  unfold jw Formalism.HermitianLatticesTheory.jIdx
  unfold idx at i1 i2
  rw [hIB.2.2.1, hIB.2.1, i1, i2, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ValuationRepresentative.vw_inv,
    hM, Matrix.det_one, ValuationRepresentative.vw_one]
  ring
end Formalism.DivisionValues
