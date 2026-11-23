-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.suppCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:10.541828+00:00
-- url     : https://prove2.me/submissions/2ba0a8bc-5e3f-49e7-8137-7a57d12ba51a

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_lu_rec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_pt_mul_pt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_lowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_upUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_mem_lowW_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Supp
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.SuppCompact := by
  intro K _ _ _ _ R hRo hRc s t ψ C _ _ e lam
  let P := pt s t
  let P' := pt s (fun b => (t b)⁻¹)
  have hPP' : P * P' = 1 := pt_mul_pt s t _ (fun b => Units.mul_inv (t b))
  have hP'P : P' * P = 1 := pt_mul_pt s _ t (fun b => Units.inv_mul (t b))
  obtain ⟨Ph, Pu, hPhc, hPuc, hPhu⟩ := lu_rec (K := K) (n := s.sum)
  let G : Matrix (Fin s.sum) (Fin s.sum) K → Matrix (Fin s.sum) (Fin s.sum) K :=
    fun M => P * Ph (P' * M) * P'
  let U : Matrix (Fin s.sum) (Fin s.sum) K → Matrix (Fin s.sum) (Fin s.sum) K :=
    fun M => Pu (P' * M)
  have hGc : Continuous G := (continuous_const.matrix_mul
    (hPhc.comp (continuous_const.matrix_mul continuous_id))).matrix_mul continuous_const
  have hUc : Continuous U := hPuc.comp (continuous_const.matrix_mul continuous_id)
  let D : Set (Matrix (Fin s.sum) (Fin s.sum) K) := {M | IsInt R M} ∩
    ({M | IsLowUni (G M)} ∩ {M | IsLowUni (P' * G M * P)} ∩ {M | IsUpUni (U M)})
  have hIntc : IsCompact {M : Matrix (Fin s.sum) (Fin s.sum) K | IsInt R M} := by
    have hset : {M : Matrix (Fin s.sum) (Fin s.sum) K | IsInt R M} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => (R : Set K) := by
      ext M
      exact ⟨fun h a _ b _ => h a b, fun h a b => h a trivial b trivial⟩
    rw [hset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  have hDc : IsCompact D := hIntc.inter_right
    (((isClosed_lowUni.preimage hGc).inter (isClosed_lowUni.preimage
      ((continuous_const.matrix_mul hGc).matrix_mul continuous_const))).inter
      (isClosed_upUni.preimage hUc))
  have hGdet : ∀ M ∈ D, (G M).det = 1 := fun M hM => isLowUni_det K hM.2.1.1
  have hUdet : ∀ M ∈ D, (U M).det = 1 := fun M hM => isUpUni_det K hM.2.2
  let gU : D → GL (Fin s.sum) K := fun M => ⟨G M.1, (G M.1).adjugate,
    by rw [Matrix.mul_adjugate, hGdet M.1 M.2, one_smul],
    by rw [Matrix.adjugate_mul, hGdet M.1 M.2, one_smul]⟩
  let uU : D → GL (Fin s.sum) K := fun M => ⟨U M.1, (U M.1).adjugate,
    by rw [Matrix.mul_adjugate, hUdet M.1 M.2, one_smul],
    by rw [Matrix.adjugate_mul, hUdet M.1 M.2, one_smul]⟩
  have hgU : Continuous gU := Units.continuous_iff.mpr
    ⟨hGc.comp continuous_subtype_val, (hGc.comp continuous_subtype_val).matrix_adjugate⟩
  have huU : Continuous uU := Units.continuous_iff.mpr
    ⟨hUc.comp continuous_subtype_val, (hUc.comp continuous_subtype_val).matrix_adjugate⟩
  have hgmem : ∀ M : D, gU M ∈ lowW K s t := fun M =>
    (mem_lowW_iff s t P' hP'P hPP' (gU M)).mpr ⟨M.2.2.1.1, M.2.2.1.2⟩
  have humem : ∀ M : D, uU M ∈ upUniG K s.sum := fun M => M.2.2.2
  let F : D → lowW K s t × upUniG K s.sum := fun M => (⟨gU M, hgmem M⟩, ⟨uU M, humem M⟩)
  have hF : Continuous F := (hgU.subtype_mk hgmem).prodMk (huU.subtype_mk humem)
  have : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  refine HasCompactSupport.intro (isCompact_range hF) ?_
  intro p hp
  have hnot : ¬ IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    intro hInt
    rcases p with ⟨⟨g, hg⟩, ⟨u, hu⟩⟩
    apply hp
    let gm : Matrix (Fin s.sum) (Fin s.sum) K := g
    let um : Matrix (Fin s.sum) (Fin s.sum) K := u
    obtain ⟨hgl, hhl⟩ := (mem_lowW_iff s t P' hP'P hPP' g).mp hg
    have hu' : IsUpUni um := hu
    have hM : P' * (gm * P * um) = (P' * gm * P) * um := by
      simp only [Matrix.mul_assoc]
    obtain ⟨hPh, hPu⟩ := hPhu _ _ hhl hu'
    have hGM : G (gm * P * um) = g := by
      show P * Ph (P' * (gm * P * um)) * P' = g
      rw [hM, hPh]
      simp only [Matrix.mul_assoc]
      rw [hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
    have hUM : U (gm * P * um) = u := by
      show Pu (P' * (gm * P * um)) = u
      rw [hM, hPu]
    have hMD : gm * P * um ∈ D :=
      ⟨hInt, ⟨⟨by rw [Set.mem_ofPred_eq, hGM]; exact hgl, by rw [Set.mem_ofPred_eq, hGM]; exact hhl⟩,
        by rw [Set.mem_ofPred_eq, hUM]; exact hu'⟩⟩
    exact ⟨⟨_, hMD⟩, Prod.ext (Subtype.ext (Units.ext hGM)) (Subtype.ext (Units.ext hUM))⟩
  rw [phi, if_neg hnot, zero_mul]
end Formalism.DoubleCosetMeasures.P
