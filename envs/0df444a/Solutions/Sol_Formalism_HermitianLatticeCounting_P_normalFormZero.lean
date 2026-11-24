-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normalFormZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.808582+00:00
-- url     : https://prove2.me/submissions/ba6312d3-0e86-4fb3-8533-2876dd3568eb

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_of_ge
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_succ
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  intro K V _ _ _ _ H r F F' c hS
  obtain ⟨hc, -, hlead, hex, -, -, hI, hI', hz⟩ := id hS
  rw [(Xa_zero F), bot_sup_eq] at hI
  rw [(Xa_zero F'), bot_sup_eq] at hI'
  have hII : F'.X = F.X := hI'.trans hI.symm
  have hsb : ∀ n, F'.Xa n = F.Xa n := by
    intro n
    induction n with
    | zero => rw [(Xa_zero F), (Xa_zero F')]
    | succ n ih =>
      by_cases hnr : n < r
      · have hsF : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F) ⟨n, hnr⟩
        have hsF' : F'.Xa (n + 1) = F'.Xa n ⊔ K ∙ F'.e (⟨n, hnr⟩ : Fin r).castSucc :=
          (Xa_succ F') ⟨n, hnr⟩
        obtain ⟨x, hxm, al, al', hF, hF'⟩ := hex ⟨n, hnr⟩ (Nat.zero_le _)
        obtain ⟨hal, hxa⟩ := id hF
        obtain ⟨hal', hxa'⟩ := id hF'
        have hx1 : x ∈ F.Xa (n + 1) := level_mem F (a := ⟨n, hnr⟩) (al := al) hF
        have hx1' : x ∈ F'.Xa (n + 1) := level_mem F' (a := ⟨n, hnr⟩) (al := al') hF'
        have hxa2 : x - al • F.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F'.Xa n := by
          rw [ih]
          exact hxa
        have hxa2' : x - al' • F'.e (⟨n, hnr⟩ : Fin r).castSucc ∈ F.Xa n := by
          rw [← ih]
          exact hxa'
        apply le_antisymm
        · rw [hsF']
          refine sup_le ((le_of_eq ih).trans ((Xa_mono F) (Nat.le_succ n))) ?_
          rw [Submodule.span_singleton_le_iff_mem]
          have h3 := Submodule.sub_mem _ hx1 ((Xa_mono F) (Nat.le_succ n) hxa2')
          rw [sub_sub_cancel] at h3
          exact (Submodule.smul_mem_iff _ hal').1 h3
        · rw [hsF]
          refine sup_le ((le_of_eq ih.symm).trans ((Xa_mono F') (Nat.le_succ n))) ?_
          rw [Submodule.span_singleton_le_iff_mem]
          have h3 := Submodule.sub_mem _ hx1' ((Xa_mono F') (Nat.le_succ n) hxa2)
          rw [sub_sub_cancel] at h3
          exact (Submodule.smul_mem_iff _ hal).1 h3
      · push_neg at hnr
        rw [Xa_of_ge F (a := n + 1) (by omega),
          Xa_of_ge F' (a := n + 1) (by omega), hII]
  have hstep : ∀ a : Fin r, F'.e a.castSucc - c • F.e a.castSucc ∈ F.Xa a.val := by
    intro a
    obtain ⟨x, hxm, al, al', hF, hF'⟩ := hex a (Nat.zero_le _)
    have hx0 : x ≠ 0 := (level_ne_zero F) hF
    obtain ⟨b, bl, bl', hFb, hF'b, -, hbl⟩ := hlead x hxm hx0
    obtain ⟨hab, hal_eq⟩ := (level_unique F) hF hFb
    obtain ⟨-, hal'_eq⟩ := (level_unique F') hF' hF'b
    obtain ⟨hal, hxa⟩ := id hF
    obtain ⟨hal', hxa'⟩ := id hF'
    have hxa2' : x - al' • F'.e a.castSucc ∈ F.Xa a.val := by
      rw [← hsb]
      exact hxa'
    have h3 := Submodule.sub_mem _ hxa hxa2'
    have hcal : al = c * al' := by rw [hal_eq, hal'_eq]; exact hbl
    have h4 : al' • (F'.e a.castSucc - c • F.e a.castSucc) ∈ F.Xa a.val := by
      convert h3 using 1
      rw [hcal, smul_sub, smul_smul, mul_comm al' c]
      abel
    exact (Submodule.smul_mem_iff _ hal').1 h4
  refine ⟨hsb, hstep, ?_⟩
  have h5 := hz
  rwa [hII, sup_idem] at h5
end Formalism.HermitianLatticeCounting.P
