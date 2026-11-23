-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levelAssemble
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:31.342399+00:00
-- url     : https://prove2.me/submissions/4baca141-f939-4d78-8c9a-54a56618f48e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_p_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_p_ci

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : LevelAssemble := by
  intro hF hP hPb hPP hN hNs P
  have z1 : zA P ∈ zfnsA P := by simp [zfnsA]
  have z2 : ziA P ∈ zfnsA P := by simp [zfnsA]
  have z3 : zbA P ∈ zfnsA P := by simp [zfnsA]
  have z4 : zbiA P ∈ zfnsA P := by simp [zfnsA]
  have z5 : ggA P ∈ zfnsA P := by simp [zfnsA]
  have z6 : ggiA P ∈ zfnsA P := by simp [zfnsA]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hF P
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hN P
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hNs P
  refine ⟨{
    p := pA P, pb := pbA P, c := cA P, ci := ciA P, cb := cbA P, cbi := cbiA P, ζ := zA P, ζi := ziA P,
    ζb := zbA P, ζbi := zbiA P, GG := ggA P, GGi := ggiA P, nab := nabA P, nabs := nabsA P, TT := (P.TT : ℂ),
    fns_comm := f0,
    c_ci := fun l => (f1 l).1, ci_c := fun l => (f1 l).2.1, cb_cbi := fun l => (f1 l).2.2.1, cbi_cb := fun l => (f1 l).2.2.2,
    ζ_ζi := f2, ζi_ζ := f3, ζb_ζbi := f4, ζbi_ζb := f5, GG_GGi := f6, GGi_GG := f7, GG_def := f8,
    p_c := fun l m => (hP P l).1 m, p_ci := fun l m => (hP P l).2.1 m,
    p_cb := fun l m => (hP P l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)), p_cbi := fun l m => (hP P l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    p_ζ := fun l => (hP P l).2.2 _ (Or.inr z1), p_ζi := fun l => (hP P l).2.2 _ (Or.inr z2),
    p_ζb := fun l => (hP P l).2.2 _ (Or.inr z3), p_ζbi := fun l => (hP P l).2.2 _ (Or.inr z4),
    p_GG := fun l => (hP P l).2.2 _ (Or.inr z5), p_GGi := fun l => (hP P l).2.2 _ (Or.inr z6),
    pb_cb := fun l m => (hPb P l).1 m, pb_cbi := fun l m => (hPb P l).2.1 m,
    pb_c := fun l m => (hPb P l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)), pb_ci := fun l m => (hPb P l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    pb_ζ := fun l => (hPb P l).2.2 _ (Or.inr z1), pb_ζi := fun l => (hPb P l).2.2 _ (Or.inr z2),
    pb_ζb := fun l => (hPb P l).2.2 _ (Or.inr z3), pb_ζbi := fun l => (hPb P l).2.2 _ (Or.inr z4),
    pb_GG := fun l => (hPb P l).2.2 _ (Or.inr z5), pb_GGi := fun l => (hPb P l).2.2 _ (Or.inr z6),
    p_p := fun l m => (hPP P l m).1, p_pb := fun l m => (hPP P l m).2.1, pb_pb := fun l m => (hPP P l m).2.2.1,
    p_nab := fun l => (hPP P l l).2.2.2.1, pb_nab := fun l => (hPP P l l).2.2.2.2.1,
    p_nabs := fun l => (hPP P l l).2.2.2.2.2.1, pb_nabs := fun l => (hPP P l l).2.2.2.2.2.2,
    nab_ζ := n1, nab_ζi := n2, nab_ζb := n3, nab_ζbi := n4, nab_GG := n5, nab_GGi := n6,
    nab_c := fun l => n7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nab_ci := fun l => n7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nab_cb := fun l => n7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nab_cbi := fun l => n7 _ (Or.inr ⟨l, rfl⟩),
    nabs_ζb := s1, nabs_ζbi := s2, nabs_ζ := s3, nabs_ζi := s4, nabs_GG := s5, nabs_GGi := s6,
    nabs_c := fun l => s7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nabs_ci := fun l => s7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nabs_cb := fun l => s7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nabs_cbi := fun l => s7 _ (Or.inr ⟨l, rfl⟩) }, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Formalism.FourierDecayAlt.P.Mx2
