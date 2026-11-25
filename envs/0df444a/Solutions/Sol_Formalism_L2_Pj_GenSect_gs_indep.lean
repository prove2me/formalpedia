-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.gs_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:48.281963+00:00
-- url     : https://prove2.me/submissions/de4e78bf-66bd-438e-bd1e-57332b3cfeca

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Theorems.Thm_P2M_Formalism_L2_Pj_GenSect_exists_pderiv_ne_zero_lt__42a374650296
import Theorems.Thm_Formalism_L2_Pj_GenSect_trdeg_CT
import Theorems.Thm_Formalism_L2_Pj_GenSect_alg_CT
import Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_aeval
import Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_gs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    AlgebraicIndependent K (gs (D := D) x j₀) := by
  classical
  by_contra hdep
  have hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧
      G.totalDegree = n := by
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨G, h1, h2⟩ := hdep
    exact ⟨_, G, h1, h2, rfl⟩
  obtain ⟨G, hG0, hGne, hGdeg⟩ := Nat.find_spec hex
  have hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree →
      aeval (gs x j₀) H = 0 → H = 0 := by
    intro H hH h0
    by_contra hne
    rw [hGdeg] at hH
    exact Nat.find_min hex hH ⟨H, h0, hne, rfl⟩
  have hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0 := by
    intro q; rw [← pderiv_aeval, hG0, map_zero]
  have hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) =
        aeval (gs x j₀) (pderiv q.1 G) -
          if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2) := by
    intro q
    simp_rw [pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with h0
    · exact Finset.sum_eq_zero fun p _ =>
        if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))
    · rw [Finset.sum_eq_single (q.1.1, j₀)]
      · exact if_pos (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)
      · intro p _ hp
        exact if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))
      · intro h; exact absurd (Finset.mem_univ _) h
  have hpos : 0 < G.totalDegree := by
    by_contra h
    have h0 : G.totalDegree = 0 := by omega
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, aeval_C] at hG0
    have hc : coeff 0 G = 0 :=
      (algebraMap K (CT Ω D j₀)).injective (by rw [hG0, map_zero])
    exact hGne (by rw [h0, hc, C_0])
  obtain ⟨p₁, hp₁ne, hp₁lt⟩ := exists_pderiv_ne_zero_lt' G hpos
  have hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0 := fun h => hp₁ne (hmin _ hp₁lt h)
  have hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp₁
    by_cases hZ : Zs j₀ p₁
    · obtain ⟨h1, h2⟩ := hZ
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h1
      have e : p₁ = (i.succ, j₀) := Prod.ext_iff.mpr ⟨hi.symm, h2⟩
      rw [e]; exact hall i
    · have h := hd ⟨p₁, hZ⟩
      rw [hsum] at h
      split_ifs at h with h0
      · rwa [sub_zero] at h
      · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
        simp only at h hi
        rw [← hi, hall i, zero_mul, sub_zero] at h
        exact h
  obtain ⟨i, hi⟩ := hexi
  have hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀) := by
    intro k
    by_cases hk : k = j₀
    · subst hk
      rw [rr, div_self hx₀, C_1]
      exact isAlgebraic_one
    · have hq : ¬ Zs j₀ (i.succ, k) := fun h => hk h.2
      have h := hd ⟨(i.succ, k), hq⟩
      rw [hsum, if_neg (Fin.succ_ne_zero i), sub_eq_zero] at h
      have m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      have m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      refine ⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun f => Polynomial.coeff f 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, if_pos, one_ne_zero, if_false, sub_zero] at h1
        exact hi (congrArg Subtype.val h1)
      · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
        exact sub_eq_zero.mpr h.symm
  have := alg_CT x j₀ halg hr
  have htb : IsTranscendenceBasis K (gs (D := D) x j₀) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀)
      (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])
  exact hdep htb.1
end Formalism.L2.Pj.GenSect
