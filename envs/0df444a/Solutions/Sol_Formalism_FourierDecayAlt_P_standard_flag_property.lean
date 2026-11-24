-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.standard_flag_property
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:41.693112+00:00
-- url     : https://prove2.me/submissions/a207202e-8108-46ad-bcad-32ba26fb6a52

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_flagSpan_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_zero_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_wpart_uh
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_colEq
import Theorems.Thm_Formalism_QuantumDeterminants_S_F
import Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x7 FlagSpanVanishing
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.SFlag := by
  intro k r z hz
  ext s
  constructor
  · rintro ⟨hs, hfl⟩
    have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        s i (eI k r a) = if i = eI k r a then 1 else 0 := by
      intro a i hi
      have h := flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)
      have hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by rw [fvec, dif_pos (by simp)]; rfl
      rw [hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero] at h
      rw [h]; simp [bvec, Pi.single_apply]
    have hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i := by
      intro i hi
      have h := flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)
      have hf : fvec k r z (Fin.last r) = z := by rw [fvec, dif_neg (by simp)]
      rw [hf, Pi.sub_apply, sub_eq_zero] at h; exact h
    have hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0 := by
      intro p j hp hj1 hj2
      have hpa : 2 * r + k - p.val < r := by omega
      have e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p := Fin.ext (by simp [esI]; omega)
      rw [← e]; exact zero_block s hs hcol j hj1 hj2 _ _ rfl
    have hhU := wpart_uh s hs hA
    set h := wpart s with hh
    have hhW : h ∈ UWset k r z := by
      refine ⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]
      · funext i
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · rw [← hzc i hi.1]
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · simp only [hh, wpart, if_pos (And.intro hi.1 (And.intro hi.2 hj))]
          · have hzj : z j = 0 := hz.1 j (by omega)
            rw [hzj, mul_zero, mul_zero]
        · simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single i]
          · simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩)]; simp
          · intro j _ hj
            simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩), if_neg (Ne.symm hj), zero_mul]
          · simp
    have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hhU
    have hblk := WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)
    refine ⟨h, hhW, h⁻¹ * s, ?_, ?_⟩
    · rw [WeylGroupFacts.nset_iff]
      refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩
      rw [Matrix.mul_apply]
      by_cases hjr : j.val < r
      · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
        have hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr)]
          · have := hcol ⟨j.val, hjr⟩ p (by simp; omega)
            rw [e, if_neg (fun e' => hpr (by rw [e']; exact hjr))] at this
            rw [this, mul_zero, mul_zero]
        simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have := hcol ⟨j.val, hjr⟩ i (by simp; omega)
        rw [e] at this; exact this
      · have hir : r ≤ i.val := by omega
        have hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr), if_neg (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]
          · by_cases hpk : p.val ≤ r + k
            · simp only [hh, wpart]
              rw [if_pos ⟨by omega, hpk, by omega, hj⟩]
            · rw [hA p j (by omega) (by omega) hj]
              simp only [hh, wpart]
              rw [if_neg (fun h' => hpk h'.2.1), if_neg (fun e' => by rw [e'] at hpk; exact hpk hj)]
        simp only [hterm]
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]
    · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  · intro hs
    refine ⟨Sset_UH hs, fun a => ?_⟩
    obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    rw [colEq hsF a]
    have hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c := by
      simp [ite_smul]
    rw [hfa, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    rw [← sub_smul]
    by_cases hca : c < a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)
    · have : U c a - (if c = a then 1 else 0) = 0 := by
        rcases eq_or_lt_of_le (not_lt.mp hca) with e | e
        · rw [← e, hU2, if_pos rfl, sub_self]
        · rw [hU1 c a e, if_neg (ne_of_gt e), sub_self]
      rw [this, zero_smul]; exact Submodule.zero_mem _
end Formalism.FourierDecayAlt.P
