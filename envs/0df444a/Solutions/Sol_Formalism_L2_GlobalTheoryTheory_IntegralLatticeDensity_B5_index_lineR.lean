-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_lineR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:52.081326+00:00
-- url     : https://prove2.me/submissions/5f34c7ca-9550-4da2-91d7-c061c447fe4d

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_CoeIdealDifferentNeZero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_coeIdeal_different_ne_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_lineR_eq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_imI


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
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (i : ι) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ lineR M emb I i) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M emb I i).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) : ℚ) : ℝ) ^
        Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    mul_ne_zero hI (coeIdeal_different_ne_zero K E)
  have heq := lineR_eq K E φ₀ M ι emb hinj hres hcard hM I i
  rw [heq] at hs ⊢
  exact index_imI M (emb i) (hM i) _ hJ s hs0 hs
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
