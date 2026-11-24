-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:51.212648+00:00
-- url     : https://prove2.me/submissions/07a2f3fb-997e-4794-823e-b92bb7ae74ab

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxFstInj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_fst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_exists_max
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_indepF
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_eq_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_ph_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_wt_can


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} {M M' : GLMod n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (F : Type) [Field F]
    (nu0 : Fin n → ℤ) :
    LinearIndependent F (fun x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} =>
      fun i => ((qx_ph ps e CF x.1 i (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ := hcon
  let s : Finset (Fin n → ℤ) := (univ.filter fun x => g x ≠ 0).image fun x => CF.mu x.1.1
  obtain ⟨mu0, hmu0, hmax⟩ := qb_exists_max s ⟨_, mem_image.2 ⟨x1, by simp [hx1], rfl⟩⟩
  obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hmu0
  replace hx0 : g x0 ≠ 0 := by simpa using hx0
  obtain ⟨k0, hk0, heps⟩ := hd.2.2.2.2.1 (CF.mu x0.1.1) (CF.dom _) x0.1.2 x0.1.2.2
  have hK : ∀ x, g x ≠ 0 → ∀ K, ps (CF.mu x.1.1) x.1.2 (K, k0) (canT (x.1.2 : Fin n → ℤ)) ≠ 0 →
      CF.mu x.1.1 = CF.mu x0.1.1 ∧ K = canT (CF.mu x.1.1) := by
    intro x hgx K hne
    have h1 := qx_wt_can hd (CF.dom _) x.1.2.2 K k0 hne
    have h2 : qb_wtT (CF.mu x.1.1) K = CF.mu x0.1.1 := by
      rw [h1, hk0, x.2, x0.2, sub_sub_cancel]
    have h3 : DomLE (CF.mu x0.1.1) (CF.mu x.1.1) := h2 ▸ qb_wtT_le (CF.dom _) K
    have h4 := hmax _ (mem_image.2 ⟨x, by simp [hgx], rfl⟩) h3
    exact ⟨h4, (qb_wtT_eq_iff (CF.dom _) K).1 (h2.trans h4.symm)⟩
  have hterm : ∀ x (i : M.ι),
      g x * ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) =
      if CF.mu x.1.1 = CF.mu x0.1.1 then
        (g x * ((ps (CF.mu x.1.1) x.1.2 (canT (CF.mu x.1.1), k0) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) *
          ((CF.ph x.1.1 i (canT (CF.mu x.1.1)) : ℤ) : F) else 0 := by
    intro x i
    by_cases hgx : g x = 0
    · simp [hgx]
    rw [qx_ph_apply]
    simp only [Equiv.apply_symm_apply]
    split_ifs with hm
    · rw [Finset.sum_eq_single (canT (CF.mu x.1.1))]
      · push_cast; ring
      · intro K _ hKne
        exact mul_eq_zero_of_right _ (by_contra fun h => hKne (hK x hgx K h).2)
      · intro h; exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero, Int.cast_zero, mul_zero]
      intro K _
      exact mul_eq_zero_of_right _ (by_contra fun h => hm (hK x hgx K h).1)
  have hrel : ∀ i : M.ι, ∑ x, g x *
      ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) = 0 := by
    intro i
    have := congrFun hg (e.symm (i, k0))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  simp only [hterm] at hrel
  have hli := (qb_indepF CF F (CF.mu x0.1.1)).comp
    (fun x : {x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} // CF.mu x.1.1 = CF.mu x0.1.1} =>
      (⟨x.1.1.1, x.2⟩ : {j : CF.J // CF.mu j = CF.mu x0.1.1}))
    (fun x y h => Subtype.ext (qx_fst_inj CF nu0 x.1 y.1 (congrArg Subtype.val h)))
  have h0 := Fintype.linearIndependent_iff.1 hli
    (fun x => g x.1 * ((ps (CF.mu x.1.1.1) x.1.1.2 (canT (CF.mu x.1.1.1), k0)
      (canT (x.1.1.2 : Fin n → ℤ)) : ℤ) : F)) ?_ ⟨x0, rfl⟩
  · simp only at h0
    rcases heps with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hx0 h0
  · funext i
    have := hrel i
    rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => CF.mu x.1.1 = CF.mu x0.1.1) _ (by simp)] at this
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp] using this
end Formalism.InvariantFactorPaths.ColumnFamilies
