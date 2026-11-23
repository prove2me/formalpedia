-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.avgDataExists_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:49.778802+00:00
-- url     : https://prove2.me/submissions/d98e6ed0-cb6c-43f3-91f5-f57160b8e49a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_exists_reps
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_lat_mem_nhds
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_modulus_positive_multiplicative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution : AvgDataExists := by
  intro hLC hKH hML hCh hLF K _ _ _ R ψ hD hn s F Om Lc hs hOm hLc
  classical
  obtain ⟨hOo, hOc, hOu, _⟩ := hOm
  have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
  obtain ⟨L₁, hl₁, hle₁, hp₁⟩ := (hCh K R ψ hD hn).1 (Om ∪ Lc) (hOc.union hLc)
  obtain ⟨V₀, hV₀, hV₀s⟩ := compact_open_separated_add_right hOc hOo (subset_refl Om)
  obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hML K R ψ hD hn Om hOc hOu Set.univ Filter.univ_mem
  choose Λ hΛ hΛp using fun h : Point K => hLC K R ψ hD hn s h Om hs hOc hOu
  have hV : (V₀ ∩ (Λ₀ : Set K)) ∩ ⋂ h ∈ F, (Λ h : Set K) ∈ 𝓝 (0 : K) :=
    Filter.inter_mem (Filter.inter_mem hV₀ (lat_mem_nhds hΛ₀))
      ((Filter.biInter_finset_mem F).2 fun h _ => lat_mem_nhds (hΛ h))
  obtain ⟨L₂, hl₂, hle₂, hp₂⟩ := (hCh K R ψ hD hn).2 _ hV
  obtain ⟨A, hA⟩ := exists_reps L₂ R.toAddSubgroup (hLF K L₂ R.toAddSubgroup hl₂ hRlat)
  obtain ⟨B, hB⟩ := exists_reps R.toAddSubgroup L₁ (hLF K R.toAddSubgroup L₁ hRlat hl₁)
  refine ⟨{ L₁ := L₁, L₂ := L₂, A := A, B := B, lat₁ := hl₁, lat₂ := hl₂, le₁ := hle₁, le₂ := hle₂,
            omPerp := fun z hz => hp₁ z (Or.inl hz), cutPerp := fun z hz => hp₁ z (Or.inr hz),
            omStable := ?_, nsInv := ?_, repsA := hA, repsB := hB }⟩
  · intro z hz l hl
    exact hV₀s (Set.add_mem_add hz (hp₂ l hl).1.1)
  · intro h hh h' hh' z hz l hl
    have hlV := hp₂ l hl
    obtain ⟨hu', hmod, _⟩ := hΛ₀p z hz l hlV.1.2
    have hu := hOu z hz
    have hlh : l ∈ Λ h := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h hh
    have hlh' : l ∈ Λ h' := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h' hh'
    unfold NsK
    rw [dif_pos hu', dif_pos hu]
    unfold Ns
    have hz0 : ((hu.unit : Kˣ) : K) ∈ Om := by rw [IsUnit.unit_spec]; exact hz
    have hd : ((hu'.unit : Kˣ) : K) - ((hu.unit : Kˣ) : K) = l := by
      rw [IsUnit.unit_spec, IsUnit.unit_spec]; ring
    have e1 : modK R (((hu'.unit : Kˣ) : K) * ((hu'.unit : Kˣ) : K)) =
        modK R (((hu.unit : Kˣ) : K) * ((hu.unit : Kˣ) : K)) := by
      rw [(modulus_positive_multiplicative K R ψ hD hu'.unit hu'.unit).2,
        (modulus_positive_multiplicative K R ψ hD hu.unit hu.unit).2, IsUnit.unit_spec, IsUnit.unit_spec, hmod]
    have e2 : Kp R ψ (addBlock h s hu'.unit) (addBlock h' s hu'.unit) =
        Kp R ψ (addBlock h s hu.unit) (addBlock h' s hu.unit) := by
      rw [hΛp h hu.unit hu'.unit hz0 (by rw [hd]; exact hlh) _,
        hKH K R ψ (addBlock h' s hu'.unit) (addBlock h s hu.unit),
        hΛp h' hu.unit hu'.unit hz0 (by rw [hd]; exact hlh') _,
        ← hKH K R ψ (addBlock h' s hu.unit) (addBlock h s hu.unit)]
    rw [e1, e2]
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
