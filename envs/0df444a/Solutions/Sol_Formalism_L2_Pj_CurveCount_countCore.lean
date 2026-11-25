-- Prove2me | solution 1 for Formalism.L2.Pj.CurveCount.countCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:28.185601+00:00
-- url     : https://prove2.me/submissions/f1422005-2ab8-43be-bc91-0dffaa9ee0ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA
import Theorems.Thm_Formalism_L2_Pj_CurveCount_aeval_div_homog
import Theorems.Thm_Formalism_L2_Pj_CurveCount_exists_indep_ratios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial
namespace Formalism.L2.Pj.CurveCount
theorem _root_.solution {K κ Ω : Type*} [Field K] [Field κ] [Field Ω] [Algebra K κ] [Algebra K Ω] {N D : ℕ}
    (v : Fin N → Ω) (x : Fin N → κ) (a : Fin N) (hva : v a ≠ 0) (hxa : x a ≠ 0)
    (htr : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun i => v i / v a)) ≤ D)
    (htrans : ∀ Q : MvPolynomial (Fin N) K, aeval (fun i => v i / v a) Q = 0 → aeval (fun i => x i / x a) Q = 0)
    (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1)
    (P : MvPolynomial (Fin N) K) {k : ℕ} (hP : P.IsHomogeneous k) (hPv : aeval v P ≠ 0) :
    aeval x P ≠ 0 := by
  classical
  intro hxP
  set ρ : Fin N → Ω := fun i => v i / v a with hρ
  set σ : Fin N → κ := fun i => x i / x a with hσ
  have hα0 : aeval ρ P ≠ 0 := by
    rw [hρ, aeval_div_homog v (v a) hP]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hva)) hPv
  have hσP : aeval σ P = 0 := by
    rw [hσ, aeval_div_homog x (x a) hP, hxP, mul_zero]
  obtain ⟨s, hscard, hsub, hind⟩ := exists_indep_ratios (K := K) x a hxa t ht hlin hlin0
  have hf : ∀ e : s, ∃ i, σ i = (e : κ) := fun e => hsub e.2
  choose f hfe using hf
  have hy : AlgebraicIndependent K (fun e : s => (e : κ)) := hind
  have h3 : (σ ∘ f) = fun e : s => (e : κ) := funext hfe
  have huind : AlgebraicIndependent K (ρ ∘ f) := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    have h1 : aeval ρ (rename f Q) = 0 := by rw [aeval_rename]; exact hQ
    have h2 := htrans (rename f Q) h1
    rw [aeval_rename, h3] at h2
    exact (algebraicIndependent_iff.mp hy) Q h2
  have hρA : ∀ i, ρ i ∈ IntermediateField.adjoin K (Set.range ρ) :=
    fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let ρA : Fin N → IntermediateField.adjoin K (Set.range ρ) := fun i => ⟨ρ i, hρA i⟩
  have hvalρ : ∀ Q : MvPolynomial (Fin N) K,
      IntermediateField.val _ (aeval ρA Q) = aeval ρ Q := by
    intro Q
    induction Q using MvPolynomial.induction_on
    next c =>
      simp only [MvPolynomial.aeval_C, AlgHom.commutes]
    next p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]
    next p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      rfl
  have hnot : ¬ AlgebraicIndependent K (fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f)) := by
    intro hI
    let w : Option s → IntermediateField.adjoin K (Set.range ρ) :=
      fun o => o.elim (aeval ρA P) (fun e => ρA (f e))
    have hcomp : (IntermediateField.val _) ∘ w = fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f) := by
      funext o
      cases o with
      | none => exact hvalρ P
      | some e => rfl
    have hw : AlgebraicIndependent K w := by
      apply AlgebraicIndependent.of_comp (IntermediateField.val _)
      rw [hcomp]
      exact hI
    have hcard := hw.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr htr)
    simp [Cardinal.mk_fintype, Fintype.card_option, hscard] at hcard
  have halg : IsAlgebraic (Algebra.adjoin K (Set.range (ρ ∘ f))) (aeval ρ P) := by
    by_contra hna
    exact hnot ((huind.option_iff_transcendental _).mpr hna)
  set α := aeval ρ P with hαdef
  have hex : ∃ n, ∃ p : Polynomial (Algebra.adjoin K (Set.range (ρ ∘ f))),
      p ≠ 0 ∧ Polynomial.aeval α p = 0 ∧ p.natDegree = n := by
    obtain ⟨p, hp0, hp⟩ := halg
    exact ⟨_, p, hp0, hp, rfl⟩
  obtain ⟨p, hp0, hpα, hpn⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hc
    have hdec : Polynomial.X * p.divX = p := by
      have h0 := Polynomial.X_mul_divX_add p
      rw [hc, map_zero, add_zero] at h0
      exact h0
    have hd0 : p.divX ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdec
      exact hp0 hdec.symm
    have hdα : Polynomial.aeval α p.divX = 0 := by
      have h1 : Polynomial.aeval α p = α * Polynomial.aeval α p.divX := by
        conv_lhs => rw [← hdec]
        rw [map_mul, Polynomial.aeval_X]
      rw [hpα] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hα0
    have hdeg : p.divX.natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have hn0 : p.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero] at hp0
        exact hp0 rfl
      omega
    exact Nat.find_min hex (hpn ▸ hdeg) ⟨p.divX, hd0, hdα, rfl⟩
  have hQ : ∀ c : Algebra.adjoin K (Set.range (ρ ∘ f)), ∃ Q : MvPolynomial s K,
      aeval (ρ ∘ f) Q = (c : Ω) := by
    intro c
    have hc : (c : Ω) ∈ (MvPolynomial.aeval (R := K) (ρ ∘ f)).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨Q, hQ⟩ := hc
    exact ⟨Q, hQ⟩
  choose Qc hQc using hQ
  have hT : aeval ρ (∑ j ∈ Finset.range (p.natDegree + 1), rename f (Qc (p.coeff j)) * P ^ j) = 0 := by
    rw [map_sum]
    simp only [map_mul, map_pow, aeval_rename, hQc]
    rw [← hpα, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hT2 := htrans _ hT
  rw [map_sum, Finset.sum_range_succ'] at hT2
  simp only [map_mul, map_pow, aeval_rename, hσP, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, mul_one] at hT2
  rw [h3] at hT2
  have h4 := (algebraicIndependent_iff.mp hy) _ hT2
  have h5 := hQc (p.coeff 0)
  rw [h4, map_zero] at h5
  apply hc0
  apply Subtype.ext
  simpa using h5.symm
end Formalism.L2.Pj.CurveCount
