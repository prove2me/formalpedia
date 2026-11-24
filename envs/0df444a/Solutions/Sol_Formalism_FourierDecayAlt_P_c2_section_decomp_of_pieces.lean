-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2_section_decomp_of_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:09.19493+00:00
-- url     : https://prove2.me/submissions/1c93a666-a984-4693-8811-72c1911ea594

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SectionDecompositionOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_N_sub_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_UW_sub_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_one_mem_UW
import Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_symmetric_group_holds
import Theorems.Thm_Formalism_QuantumDeterminants_unipotent_subgroup_holds
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_weyl_normal_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x7
set_option maxHeartbeats 400000
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.SectionDecompOfParts := by
  intro _ hC1iii hURI hUp _ hUM _ hTM k r z z' γ hstd hpos hmono s hs
  have hz := hstd.2.1
  have hU := hUM k r z hz
  have hSg := symmetric_group_holds k r z hz.1
  have hNg := unipotent_subgroup_holds k r

  have hu1 : C2.uMap k r z 1 = 1 := hU.2 1 (one_mem_UW z)
  have huinv : ∀ x ∈ Sset k r z, C2.uMap k r z x⁻¹ = (C2.uMap k r z x)⁻¹ := by
    intro x hx
    have hxi := hSg.2.2 x hx
    have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hx)
    have : C2.uMap k r z x * C2.uMap k r z x⁻¹ = 1 := by
      rw [← (hU.1 x hx).2.2 _ hxi, Matrix.mul_nonsing_inv _ hxu, hu1]
    exact (Matrix.inv_eq_right_inv this).symm

  have huSg : ∀ σ ∈ C2.Sg k r z z' γ, σ ∈ Sset k r z ∧ ∃ v, v ∈ C2.UTset (r + 1) ∧ vᴴ ∈ C2.LPg (Zhat k r z z' γ) ∧
      C2.uMap k r z σ = v := by
    rintro σ ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
    have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
    have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
    have hhS : h ∈ Sset k r z := UW_sub_S hh
    have hs1 := hSg.2.1 _ hn0S _ hτS
    refine ⟨hSg.2.1 _ hs1 _ hhS, v, hv, hvL, ?_⟩
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul, Matrix.mul_one]

  have hRimg : ∀ ρ ∈ C2.Rst k r z z' γ, C2.uMap k r z ρ ∈ C2.UTset (r + 1) ∧ (C2.uMap k r z ρ)ᴴ ∈ C2.Lstg (Zhat k r z z' γ) := by
    intro ρ hρ
    have hmap := (hC1iii k r z z' γ hstd hpos).1.mapsTo hρ
    obtain ⟨h1, h2, h3⟩ := hmap
    have : C2.uMap k r z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} :=
      ⟨h1, _, h2, h3⟩
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono] at this
    exact this
  have hRS : ∀ ρ ∈ C2.Rst k r z z' γ, ρ ∈ Sset k r z := fun ρ hρ => hρ.1.1
  obtain ⟨hus, husUT, _⟩ := hU.1 s hs
  obtain ⟨⟨uρ, v⟩, ⟨huρ, hv, huρL, hvL, hue⟩, huniq⟩ := hUp (r + 1) (Zhat k r z z' γ) hmono _ husUT
  simp only at huρ hv huρL hvL hue

  have huρR : uρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} := by
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono]; exact ⟨huρ, huρL⟩
  obtain ⟨u', hu', hu'e⟩ := huρR.2
  have hmemT : (uρ, u') ∈ {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
      p.1 ∈ C2.UTset (r + 1) ∧ p.2 ∈ C2.UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨huρ, hu', hu'e⟩
  obtain ⟨ρ, hρ, hρe⟩ := (hC1iii k r z z' γ hstd hpos).1.surjOn hmemT
  have hρu : C2.uMap k r z ρ = uρ := congrArg Prod.fst hρe
  have hρS := hRS ρ hρ
  have hρu' : IsUnit ρ.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hρS)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ρ⁻¹ * s := ⟨_, rfl⟩
  have hσS : σ ∈ Sset k r z := by rw [hσ]; exact hSg.2.1 _ (hSg.2.2 _ hρS) _ hs
  have hσu : C2.uMap k r z σ = v := by
    rw [hσ, (hU.1 _ (hSg.2.2 _ hρS)).2.2 s hs, huinv ρ hρS, hρu, hue, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (C2x2.ut_unit huρ), Matrix.one_mul]
  obtain ⟨h1, hh1, n1, hn1, hσe⟩ := hσS
  have hh1S := UW_sub_S hh1
  have hn1S := N_sub_S (z := z) hn1
  have hn1u : C2.uMap k r z n1 = v := by
    rw [← hσu, hσe, (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1, Matrix.one_mul]
  have hh1inv := WeylGroupFacts.uw_inv hh1
  have hh1u : IsUnit h1.det := WeylGroupFacts.isUnit_of_uh hh1.1
  have hn2 : h1 * n1 * h1⁻¹ ∈ Nset k r := (unitary_weyl_normal_holds k r z hz.1 h1 hh1 n1 hn1).1
  have hn2u : C2.uMap k r z (h1 * n1 * h1⁻¹) = v := by
    rw [(hU.1 _ (hSg.2.1 _ hh1S _ hn1S)).2.2 _ (UW_sub_S hh1inv), (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1,
      hU.2 _ hh1inv, hn1u, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  obtain ⟨τv, hτv⟩ : ∃ τv, τv = C2.tauM k r z v := ⟨_, rfl⟩
  rw [← hτv] at hτN hτu
  have hτS : τv ∈ Sset k r z := N_sub_S hτN
  have hτunit : IsUnit τv.det := WeylGroupFacts.isUnit_of_uh hτN.1
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = h1 * n1 * h1⁻¹ * τv⁻¹ := ⟨_, rfl⟩
  have hn0N : n0 ∈ Nset k r := by rw [hn0]; exact hNg.2.1 _ hn2 _ (hNg.2.2 _ hτN)
  have hn0u : C2.uMap k r z n0 = 1 := by
    rw [hn0, (hU.1 _ (N_sub_S hn2)).2.2 _ (hSg.2.2 _ hτS), huinv _ hτS, hn2u, hτu,
      Matrix.mul_nonsing_inv _ (C2x2.ut_unit hv)]
  have hσdec : σ = n0 * τv * h1 := by
    rw [hσe, hn0, Matrix.mul_assoc (h1 * n1 * h1⁻¹), Matrix.nonsing_inv_mul _ hτunit, Matrix.mul_one,
      Matrix.mul_assoc (h1 * n1), Matrix.nonsing_inv_mul _ hh1u, Matrix.mul_one]
  have hσSg : σ ∈ C2.Sg k r z z' γ := ⟨n0, ⟨hn0N, hn0u⟩, v, hv, hvL, h1, hh1, by rw [hσdec, hτv]⟩
  refine ⟨(ρ, σ), ⟨hρ, hσSg, ?_⟩, ?_⟩
  · show s = ρ * σ
    rw [hσ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu', Matrix.one_mul]
  · rintro ⟨ρ', σ'⟩ ⟨hρ', hσ', hse⟩
    simp only at hρ' hσ' hse
    obtain ⟨hσ'S, v', hv', hv'L, hσ'u⟩ := huSg σ' hσ'
    obtain ⟨hρ'U, hρ'L⟩ := hRimg ρ' hρ'
    have hus' : C2.uMap k r z s = C2.uMap k r z ρ' * v' := by
      rw [hse, (hU.1 _ (hRS ρ' hρ')).2.2 _ hσ'S, hσ'u]
    have := huniq (C2.uMap k r z ρ', v') ⟨hρ'U, hv', hρ'L, hv'L, hus'⟩
    rw [Prod.ext_iff] at this
    simp only at this
    have hρρ : ρ' = ρ := (hC1iii k r z z' γ hstd hpos).2.1 hρ' hρ (this.1.trans hρu.symm)
    subst hρρ
    have hρ'u : IsUnit ρ'.det := hρu'
    have : σ' = ρ'⁻¹ * s := by
      rw [hse, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ'u, Matrix.one_mul]
    rw [this, hσ]
end Formalism.FourierDecayAlt.P
