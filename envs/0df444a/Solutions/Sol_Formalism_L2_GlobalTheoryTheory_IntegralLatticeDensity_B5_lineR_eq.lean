-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.lineR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:31.208624+00:00
-- url     : https://prove2.me/submissions/239e78b4-d775-405a-b911-c1bdf4841b97

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_CoeIdealDifferentNeZero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_dual_eq_inv_mul_different
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_coeIdeal_different_ne_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_mem_imI_iff
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_mem_mmR_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) :
    lineR M emb I i = imI M (emb i) (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) := by
  have h0 : liftM M 0 = 0 := by
    rw [liftM, dif_pos (zero_mem M)]
    rfl
  by_cases hI : I = 0
  · subst hI
    rw [zero_mul]
    have hm : mmR M emb (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [mmR, Submodule.span_eq_bot]
      rintro v ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      funext k
      simp [h0]
    have hR : imI M (emb i) (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [imI, Submodule.span_eq_bot]
      rintro y ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      simp [h0]
    rw [hR, lineR, hm]
    ext x
    simp
  · have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
      mul_ne_zero hI (coeIdeal_different_ne_zero K E)
    ext x
    rw [lineR, Submodule.mem_comap, mem_mmR_iff K E φ₀ M ι emb hinj hres hcard hM I hI,
      mem_imI_iff M (emb i) (hM i) _ hJ, ← dual_eq_inv_mul_different K E I]
    refine forall₂_congr fun b _ => ?_
    simp [Pi.single_apply]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
