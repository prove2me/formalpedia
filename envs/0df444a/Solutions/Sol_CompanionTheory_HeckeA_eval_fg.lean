-- Prove2me | solution 1 for CompanionTheory.HeckeA.eval_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.628802+00:00
-- url     : https://prove2.me/submissions/413c6e7b-5593-4073-9831-afbd3e409d7e

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_UpperTheory_Reformulated_B_Qn15_eval_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
variable {K}
variable {R : Type} [CommRing R] [Algebra R ℂ]
namespace CompanionTheory.HeckeA
theorem _root_.solution {σ : Type} {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (P : MvPolynomial σ ℂ) :
    ∃ M : Submodule R ℂ, M.FG ∧ ∀ v : σ → ℂ, (∀ i, v i ∈ M₀) → MvPolynomial.eval v P ∈ M :=
  _root_.UpperTheory.Reformulated.B.Qn15.eval_fg h₀ P
end CompanionTheory.HeckeA
