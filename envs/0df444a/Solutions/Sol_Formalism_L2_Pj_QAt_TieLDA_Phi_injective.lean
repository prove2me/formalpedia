-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.Phi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:19.755232+00:00
-- url     : https://prove2.me/submissions/f2ff8286-0279-4d3d-8eb0-1ea0613fffb4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_tmul
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_isTorsionFree_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (X : Submodule R U) (hX : X.FG) : Function.Injective (Phi T hRT X) := by
  classical
  haveI : Module.Finite R X := Module.Finite.iff_fg.2 hX
  haveI : Module.IsTorsionFree R X := isTorsionFree_sub (K := K) X
  haveI : Module.Free R X := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R X
  let v : Module.Free.ChooseBasisIndex R X → K₁ ⊗[K] U := fun i => tm K K₁ ((b i : X) : U)
  have hR : LinearIndependent R (fun i => ((b i : X) : U)) :=
    b.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hK : LinearIndependent K (fun i => ((b i : X) : U)) := (LinearIndependent.iff_fractionRing R K).1 hR
  have hK₁ : LinearIndependent K₁ v := Module.Flat.linearIndependent_one_tmul hK
  have hT : LinearIndependent T v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := (linearIndependent_iff'.1 hK₁) s (fun j => (g j : K₁)) (by exact hg) i hi
    exact Subtype.ext h1
  let b' := b.baseChange T
  have hcomp : (Phi T hRT X) ∘ₗ b'.repr.symm.toLinearMap = Finsupp.linearCombination T v := by
    refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
    simp [b', v, Basis.baseChange_apply, Phi_tmul]
    first
      | exact (one_smul _ _).symm
      | (rw [smulT_def]; simp)
  have key : ∀ z, Finsupp.linearCombination T v (b'.repr z) = Phi T hRT X z := by
    intro z
    rw [← hcomp]
    simp
  intro z w hzw
  apply b'.repr.injective
  exact hT (by rw [key, key, hzw])
end Formalism.L2.Pj.QAt.TieLDA
