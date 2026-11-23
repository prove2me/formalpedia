-- Prove2me | solution 1 for Formalism.L2.Col.GSD.stab_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:51.331383+00:00
-- url     : https://prove2.me/submissions/700aa8c0-75b6-40aa-bf1b-089d73202516

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
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution {Γ H D : Type} [Group Γ] [Group H] [MulAction (Γ × H) D]
    (free : ∀ (h : H) (d : D), ((1, h) : Γ × H) • d = d → h = 1) (d : D) :
    Function.Injective (fun x : MulAction.stabilizer (Γ × H) d => (x : Γ × H).1) := by
  intro x y hxy
  have hxy' : (x : Γ × H).1 = (y : Γ × H).1 := hxy
  set z : Γ × H := (x : Γ × H)⁻¹ * (y : Γ × H) with hzdef
  have hz : z • d = d := by
    rw [hzdef, mul_smul, MulAction.mem_stabilizer_iff.mp y.2, inv_smul_eq_iff, MulAction.mem_stabilizer_iff.mp x.2]
  have h1 : z.1 = 1 := by
    rw [hzdef, Prod.fst_mul, Prod.fst_inv, ← hxy', inv_mul_cancel]
  have h3 : ((1, z.2) : Γ × H) = z := Prod.ext h1.symm rfl
  have h2 : z.2 = 1 := free z.2 d (by rw [h3]; exact hz)
  have h4 : z = 1 := Prod.ext h1 h2
  exact Subtype.ext (inv_mul_eq_one.mp h4)
end Formalism.L2.Col.GSD
