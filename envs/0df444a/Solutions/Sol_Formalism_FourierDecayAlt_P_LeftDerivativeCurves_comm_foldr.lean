-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.comm_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:17.08829+00:00
-- url     : https://prove2.me/submissions/034dbf87-0052-4312-8df2-16716335757b

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace LeftDerivativeCurves
open Qx2 (Good)
section Analysis
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Analysis
section Comm
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
private theorem smoothLev_foldr_of_good (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, Good k r i D T)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact (hL T List.mem_cons_self).sm _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))
end Comm
section Conj
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
end Conj
end LeftDerivativeCurves
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {B : (Mx k r → E) → Mx k r → E} (L : List ((Mx k r → E) → Mx k r → E))
    (hL : ∀ T ∈ L, Good k r i D T) (hc : ∀ T ∈ L, Comm k r i D B T) :
    Comm k r i D B (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact (comm_id B).symm
  | cons T L ih =>
    intro f hf x hx
    have hT := hL T List.mem_cons_self
    have hL' : ∀ S ∈ L, Good k r i D S := fun S hS => hL S (List.mem_cons_of_mem _ hS)
    have hc' : ∀ S ∈ L, Comm k r i D B S := fun S hS => hc S (List.mem_cons_of_mem _ hS)
    show B (T (L.foldr (fun T h => T h) f)) x = T (L.foldr (fun T h => T h) (B f)) x
    rw [hc T List.mem_cons_self _ (smoothLev_foldr_of_good L hL' f hf) x hx]
    exact hT.loc _ _ (fun y hy => ih hL' hc' f hf y hy) x hx
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
