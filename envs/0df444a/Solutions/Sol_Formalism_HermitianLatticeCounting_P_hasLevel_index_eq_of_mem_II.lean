-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hasLevel_index_eq_of_mem_II
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:10.570453+00:00
-- url     : https://prove2.me/submissions/6240f1ac-7c24-4f0f-9f07-11d135a1af6f

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_succ_eq_castSucc
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_succ_eq_last

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
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F F' : FlagD H r) (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) (hμ : ∃ μ : K, μ + star μ ≠ 0) (hrel : Relevant F F') :
    ∀ (k : ℕ) (x : V) (a a' : Fin r) (al al' : K), a.val + 1 + k = r → x ∈ II F F' →
      F.HasLevel x a al → F'.HasLevel x a' al' →
      a = a' ∧ F'.z - (al / al') • F.z ∈ F.X ⊔ F'.X ∧
      ∀ b : Fin r, a.val ≤ b.val → ∃ y ∈ II F F', F.HasLevel y b al ∧ F'.HasLevel y b al' := by
  intro k
  induction k with
  | zero =>
    intro x a a' al al' hk hx hF hF'
    have ha : a.val + 1 = r := by omega
    have hstep := hStep K V H r F F' x a a' al al' hμ hrel hx hF hF'
    have hsa : a.succ = Fin.last r := succ_eq_last a ha
    obtain ⟨hal, -⟩ := id hF
    obtain ⟨hal', -⟩ := id hF'
    have h3 : F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1) ≤ F.X ⊔ F'.X :=
      sup_le_sup ((Xa_le_X F) _) ((Xa_le_X F') _)
    have haa' : a = a' := by
      by_contra hne
      have hne' : a'.val ≠ a.val := fun h => hne (Fin.ext h).symm
      have ha'lt : a'.val + 1 < r := by have := a'.isLt; omega
      have hsa' : a'.succ = (⟨a'.val + 1, ha'lt⟩ : Fin r).castSucc := succ_eq_castSucc a' ha'lt
      have h2 : al' • F'.e a'.succ ∈ F.X ⊔ F'.X := by
        rw [hsa']
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ ((e_mem_X F') _))
      have h4 := Submodule.add_mem _ (h3 hstep) h2
      rw [sub_add_cancel, hsa] at h4
      exact hN0 K V H r F F' ((Submodule.smul_mem_iff _ hal).1 h4)
    subst haa'
    refine ⟨rfl, ?_, fun b hb => ⟨x, hx, ?_⟩⟩
    · have h4 := Submodule.smul_mem _ (-(al')⁻¹) (h3 hstep)
      rw [hsa] at h4
      convert h4 using 1
      show F'.e (Fin.last r) - (al / al') • F.e (Fin.last r) = _
      rw [smul_sub, smul_smul, smul_smul, show -(al')⁻¹ * al' = -1 by rw [neg_mul, inv_mul_cancel₀ hal'],
        show -(al')⁻¹ * al = -(al / al') by ring]
      simp only [neg_smul, one_smul]
      abel
    · have hba : b = a := Fin.ext (by have := b.isLt; have := Fin.le_iff_val_le_val.1 hb; omega)
      subst hba
      exact ⟨hF, hF'⟩
  | succ k ih =>
    intro x a a' al al' hk hx hF hF'
    have ha1 : a.val + 1 < r := by omega
    have hsa : a.succ = (⟨a.val + 1, ha1⟩ : Fin r).castSucc := succ_eq_castSucc a ha1
    have hstep := hStep K V H r F F' x a a' al al' hμ hrel hx hF hF'
    obtain ⟨hal, -⟩ := id hF
    obtain ⟨hal', -⟩ := id hF'
    obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.1 hstep
    have hae : al • F.e a.succ = s + s' + al' • F'.e a'.succ := by
      rw [hss]
      abel
    by_cases ha'1 : a'.val + 1 < r
    · have hsa' : a'.succ = (⟨a'.val + 1, ha'1⟩ : Fin r).castSucc := succ_eq_castSucc a' ha'1
      obtain ⟨y, hydef⟩ : ∃ y : V, y = al • F.e a.succ - s := ⟨_, rfl⟩
      have hy2 : y = al' • F'.e a'.succ + s' := by
        rw [hydef, hae]
        abel
      have hyF : y ∈ F.X := by
        rw [hydef, hsa]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ((e_mem_X F) _)) ((Xa_le_X F) _ hs)
      have hyF' : y ∈ F'.X := by
        rw [hy2, hsa']
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ ((e_mem_X F') _)) ((Xa_le_X F') _ hs')
      have hyM : y ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hyF, hyF'⟩
      have hyHF : F.HasLevel y ⟨a.val + 1, ha1⟩ al := by
        unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
        refine ⟨hal, ?_⟩
        rw [hydef, ← hsa]
        simpa using hs
      have hyHF' : F'.HasLevel y ⟨a'.val + 1, ha'1⟩ al' := by
        unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
        refine ⟨hal', ?_⟩
        rw [hy2, ← hsa']
        simpa using hs'
      obtain ⟨h1, h2, h3⟩ := ih y ⟨a.val + 1, ha1⟩ ⟨a'.val + 1, ha'1⟩ al al'
        (show a.val + 1 + 1 + k = r by omega) hyM hyHF hyHF'
      have haa' : a = a' := Fin.ext (by have h5 : a.val + 1 = a'.val + 1 := congrArg Fin.val h1; omega)
      refine ⟨haa', h2, fun b hb => ?_⟩
      by_cases hba : b = a
      · subst hba
        refine ⟨x, hx, hF, ?_⟩
        rw [haa']
        exact hF'
      · have hne : b.val ≠ a.val := fun h => hba (Fin.ext h)
        exact h3 b (Fin.le_iff_val_le_val.2 (show a.val + 1 ≤ b.val by have := Fin.le_iff_val_le_val.1 hb; omega))
    · have ha'r : a'.val + 1 = r := by have := a'.isLt; omega
      have hsa' : a'.succ = Fin.last r := succ_eq_last a' ha'r
      exfalso
      apply hN0 K V H r F' F
      have h4 : al' • F'.e a'.succ = al • F.e a.succ - s - s' := by
        rw [hae]
        abel
      have h5 : al • F.e a.succ - s - s' ∈ F'.X ⊔ F.X := by
        rw [hsa]
        exact Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ ((e_mem_X F) _)))
          (Submodule.mem_sup_right ((Xa_le_X F) _ hs)))
          (Submodule.mem_sup_left ((Xa_le_X F') _ hs'))
      rw [← h4, hsa'] at h5
      exact (Submodule.smul_mem_iff _ hal').1 h5
end Formalism.HermitianLatticeCounting.P
