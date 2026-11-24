-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.exists_presc_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:38.666804+00:00
-- url     : https://prove2.me/submissions/ab645a26-b9dd-4169-9870-fcc0d99e2fb8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily
import Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_bin_step_gen
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_GluingBases_TotPos_ne_zero__13b51f779000
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_ortho_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermRepUnram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram]
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ x y, star (h x y) = h y x)
    (hpos : ∀ x, x ≠ 0 → TotPos (h x x)) :
    ∀ k : ℕ, k + 1 ≤ finrank K V → ∀ t : Fin (k + 1) → K, (∀ i, star (t i) = t i) →
      (∀ i, TotPos (t i)) →
      ∃ v : Fin (k + 1) → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        (∀ i, i ≠ Fin.last k → h (v i) (v i) = t i) ∧ v (Fin.last k) ≠ 0 := by
  have hz : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hsym, e, star_zero]
  intro k
  induction k with
  | zero =>
    intro hk t _ _
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsub : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
    exact ⟨fun _ => x, fun i j hij => absurd (hsub i j) hij,
      fun i hi => absurd (hsub i _) hi, hx⟩
  | succ k ih =>
    intro hk t hts htp
    obtain ⟨v, ho, h1, hl⟩ := ih (by omega) (fun i => t (Fin.castSucc i)) (fun i => hts _)
      (fun i => htp _)
    obtain ⟨z, hz0, hzv⟩ := GramDeterminantPositive.exists_ortho_ne_zero h v (by omega)
    obtain ⟨x, y, hxy⟩ := hermRepUnram K hK (h (v (Fin.last k)) (v (Fin.last k))) (h z z)
      (t (Fin.castSucc (Fin.last k))) (hsym _ _) (hsym _ _) (hts _) (hpos _ hl) (hpos _ hz0) (htp _)
    obtain ⟨b1, b2, b3⟩ := bin_step_gen h hz (v (Fin.last k)) z _ _ x y _ (hzv _) rfl rfl
      (hsym _ _) (hsym _ _) hxy
    set a := h (v (Fin.last k)) (v (Fin.last k)) with ha
    set b := h z z with hb
    set f₁ := x • v (Fin.last k) + y • z with hf₁
    set f₂ := (star y * b) • v (Fin.last k) - (star x * a) • z with hf₂
    have hf₂0 : f₂ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at b3
      exact mul_ne_zero (mul_ne_zero (TotPos.ne_zero' (hpos _ hl)) (TotPos.ne_zero' (hpos _ hz0)))
        (TotPos.ne_zero' (htp _)) b3.symm
    have c1 : ∀ i, i ≠ Fin.last k → h (v i) f₁ = 0 := by
      intro i hi
      rw [hf₁, map_add, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, add_zero]
    have c2 : ∀ i, i ≠ Fin.last k → h (v i) f₂ = 0 := by
      intro i hi
      rw [hf₂, map_sub, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, sub_zero]
    let u : Fin (k + 1) → V := Function.update v (Fin.last k) f₁
    have ul : u (Fin.last k) = f₁ := Function.update_self _ _ _
    have un : ∀ i, i ≠ Fin.last k → u i = v i := fun i hi => Function.update_of_ne hi _ _
    have uo : ∀ i j, i ≠ j → h (u i) (u j) = 0 := by
      intro i j hij
      by_cases hi : i = Fin.last k
      · have hj : j ≠ Fin.last k := fun e => hij (hi.trans e.symm)
        rw [hi, ul, un j hj]
        exact hz _ _ (c1 j hj)
      · by_cases hj : j = Fin.last k
        · rw [hj, ul, un i hi]; exact c1 i hi
        · rw [un i hi, un j hj]; exact ho i j hij
    have u1 : ∀ i, h (u i) (u i) = t (Fin.castSucc i) := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b1
      · rw [un i hi]; exact h1 i hi
    have u2 : ∀ i, h (u i) f₂ = 0 := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b2
      · rw [un i hi]; exact c2 i hi
    refine ⟨Fin.snoc u f₂, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hz _ _ (u2 j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact u2 i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact uo i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hi; exact absurd rfl hi
      · intro _
        rw [Fin.snoc_castSucc]; exact u1 i
    · rw [Fin.snoc_last]; exact hf₂0
end Formalism.L2.SG.Pf.GluingBases
