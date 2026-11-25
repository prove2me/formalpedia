-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.box_limit_of_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:04.676432+00:00
-- url     : https://prove2.me/submissions/b540833c-c55e-4945-b669-45c18dc3d5bd

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem onBoxes_ofFn_of_mem_box (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) → S.OnBoxes (List.ofFn Y) := by
  intro N
  induction N with
  | zero =>
    intro Y _
    rw [List.ofFn_zero]
    exact trivial
  | succ N ih =>
    intro Y hY
    rw [List.ofFn_succ]
    show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)
    refine ⟨?_, ih _ (fun i => ?_)⟩
    · convert hY 0 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    · convert hY i.succ using 2
      simp only [Fin.val_succ]
      omega
private theorem mem_box_of_onBoxes_ofFn (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) → ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero =>
    intro Y _ a
    exact a.elim0
  | succ N ih =>
    intro Y hY a
    rw [List.ofFn_succ] at hY
    have hY' : Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧
        S.OnBoxes (List.ofFn fun i => Y i.succ) := hY
    induction a using Fin.cases with
    | zero =>
      convert hY'.1 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    | succ i =>
      convert ih _ hY'.2 i using 2
      simp only [Fin.val_succ]
      omega
private theorem le_boxLimitFromClaim_proof : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := by
  intro hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hClaim w hw hlen
  suffices h : ∀ (N : ℕ) (Y : Fin N → ℝ), S.OnBoxes (List.ofFn Y) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn)) by
    have h' := h w.length w.get (by rw [List.ofFn_get]; exact hw) hlen
    rw [List.ofFn_get] at h'
    exact h'
  intro N Y hOn hN
  have hInt : ∀ Y' : Fin N → ℝ, (S.fam N).On Y' →
      MeasureTheory.Integrable
        (Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
    intro Y' hY'
    have hOn' : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' (fun a => by
      have h := hY' a
      rw [S.fam_J] at h
      exact h)
    have hc := (hClaim (List.ofFn Y') hOn' (by rw [List.length_ofFn]; exact hN)).1
    have hfun : S.dens (List.ofFn Y') =
        fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) ω :=
      funext (S.fam_dens N Y')
    rw [hfun] at hc
    exact hc
  have hJinf : ∀ a, ((S.fam N).J a).Infinite := by
    intro a
    rw [S.fam_J]
    exact Set.Icc_infinite (by linarith)
  have hOnF : ∀ a, Y a ∈ (S.fam N).J a := by
    intro a
    have h := mem_box_of_onBoxes_ofFn S N Y hOn a
    rw [S.fam_J]
    exact h
  have hlim := hLB hLA hLL2 hPL hCL2 hLeib hCut S.B N (S.fam N) S.c hJinf (hFam N hN) hInt Y hOnF
  have hval : S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn =
      ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (S.fam N).u) ω ∂S.B.μ := by
    rw [← (hClaim (List.ofFn Y) hOn (by rw [List.length_ofFn]; exact hN)).2]
    exact congrArg (MeasureTheory.integral S.B.μ) (funext fun ω => S.fam_dens N Y ω)
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hThm N Y hN hOn ε hε).symm
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := Formalism.FourierDecayAlt.P.LEx2.le_boxLimitFromClaim_proof
end Formalism.FourierDecayAlt.P
