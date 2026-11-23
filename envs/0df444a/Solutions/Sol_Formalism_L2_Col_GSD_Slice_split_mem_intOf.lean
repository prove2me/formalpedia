-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.split_mem_intOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:19.044148+00:00
-- url     : https://prove2.me/submissions/2aa5849c-dbdf-44f4-a6a9-00c8afc9dcbc

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]
namespace Formalism.L2.Col.GSD.Slice
theorem _root_.solution (N : S.D → Submodule (𝓞 K) S.V) (hN : ∀ (b : A) (d : S.D), N (b • d) = N d) (φ : S.EqFun) :
    φ ∈ S.intOf N ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intOf (fun t => N ((t : σ.T) : S.D)) := by
  constructor
  · intro hφ b t
    show (φ : S.D → S.V) (b • (t : S.D)) ∈ N (t : S.D)
    rw [← hN b]
    exact hφ _
  · intro H d
    have h1 : (φ : S.D → S.V) ((σ.a d)⁻¹ • σ.a d • d) ∈ N (σ.a d • d) := H (σ.a d)⁻¹ ⟨σ.a d • d, σ.a_mem d⟩
    rw [inv_smul_smul, hN] at h1
    exact h1
end Formalism.L2.Col.GSD.Slice
