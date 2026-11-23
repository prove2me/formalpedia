-- Prove2me | solution 1 for CompanionTheory.HeckeA.apply_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:50:48.026796+00:00
-- url     : https://prove2.me/submissions/2d5cbc32-fe34-4b41-8dc3-6ded4209e077

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_CompanionTheory_HeckeA_eval_fg
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
theorem _root_.solution [Module R W] [IsScalarTower R ℂ W] {σ κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ W)
    (P : κ → κ → MvPolynomial σ ℂ) {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (w : W) :
    ∃ N : Submodule R W, N.FG ∧ ∀ (A : W →ₗ[ℂ] W) (v : σ → ℂ), (∀ i, v i ∈ M₀) →
      (LinearMap.toMatrix b b A = fun i j => MvPolynomial.eval v (P i j)) → A w ∈ N := by
  choose M h1 h2 using fun p : κ × κ => eval_fg h₀ (P p.1 p.2)
  refine ⟨⨆ p : κ × κ, (M p).map ((LinearMap.toSpanSingleton ℂ W (b.repr w p.2 • b p.1)).restrictScalars R),
    Submodule.fg_iSup _ fun p => (h1 p).map _, fun A v hv hA => ?_⟩
  rw [← b.sum_repr (A w)]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [show b.repr (A w) i = ∑ j, LinearMap.toMatrix b b A i j * b.repr w j from
    (congrFun (LinearMap.toMatrix_mulVec_repr b b A w) i).symm, Finset.sum_smul]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem (i, j) ⟨_, h2 (i, j) v hv, ?_⟩
  rw [hA, mul_smul]
  rfl
end CompanionTheory.HeckeA
