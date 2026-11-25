-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.swap_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:25.626214+00:00
-- url     : https://prove2.me/submissions/2d309ea6-e994-4072-ba6a-97f02f94ef06

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_foldr
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {g₀ : Mx k r} (hg₀ : g₀ ∈ Glev k r i ∩ D)
    (L : List (((Mx k r → E) → Mx k r → E) × ((Mx k r → E) → Mx k r → E)))
    (hA : ∀ p ∈ L, Good k r i D p.1) (hB : ∀ p ∈ L, Good k r i D p.2)
    (hpt : ∀ p ∈ L, ∀ f, p.1 f g₀ = p.2 f g₀) (hc : ∀ p ∈ L, ∀ q ∈ L, Comm k r i D q.2 p.1) :
    ∀ f, SmoothLev k r i D f →
      (L.map Prod.fst).foldr (fun T h => T h) f g₀ = (L.map Prod.snd).foldl (fun h T => T h) f g₀ := by
  induction L with
  | nil => intro f _; rfl
  | cons p L ih =>
    intro f hf
    have hA' : ∀ q ∈ L, Good k r i D q.1 := fun q hq => hA q (List.mem_cons_of_mem _ hq)
    have hB' : ∀ q ∈ L, Good k r i D q.2 := fun q hq => hB q (List.mem_cons_of_mem _ hq)
    have hpt' : ∀ q ∈ L, ∀ f, q.1 f g₀ = q.2 f g₀ := fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    have hc' : ∀ q ∈ L, ∀ q' ∈ L, Comm k r i D q'.2 q.1 := fun q hq q' hq' =>
      hc q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')
    have hcomm : Comm k r i D p.2 (fun f => (L.map Prod.fst).foldr (fun T h => T h) f) :=
      comm_foldr _ (fun T hT => by obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT; exact hA' q hq)
        (fun T hT => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hT
          exact hc q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)
    exact (hpt p List.mem_cons_self _).trans ((hcomm f hf g₀ hg₀).trans
      (ih hA' hB' hpt' hc' (p.2 f) ((hB p List.mem_cons_self).sm f hf)))
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
