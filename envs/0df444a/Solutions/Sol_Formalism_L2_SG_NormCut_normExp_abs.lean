-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.normExp_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:04.39714+00:00
-- url     : https://prove2.me/submissions/3d2740a7-011d-4e71-b41d-5d5902ba5ae8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
import Theorems.Thm_Formalism_L2_SG_NormCut_gamOf_comm
import Theorems.Thm_Formalism_L2_SG_NormCut_orbitSum2
import Theorems.Thm_Formalism_L2_SG_NormCut_inner_sum_smul
import Theorems.Thm_Formalism_L2_SG_NormCut_fForm_left
import Theorems.Thm_Formalism_L2_SG_NormCut_fForm_right
import Theorems.Thm_Formalism_L2_SG_NormCut_fForm_sum
import Theorems.Thm_Formalism_L2_SG_NormCut_card_ne_zero_of_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type} [Group I] [Fintype I]
set_option maxHeartbeats 800000
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {τ Rw H K Q1 Q2 R R' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype Q1] [Fintype Q2] [Fintype R]
    [Fintype R'] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H (PiLp 2 (fun _ : Q1 × Q2 => K))) (S : Set τ)
    (lamR : R → Q1) (lamR' : R' → Q2) (Bl : R → R' → H →L[ℂ] K)
    (hBl : ∀ x y : H, inner ℂ x y = ∑ ρ, ∑ ρ', inner ℂ (Bl ρ ρ' x) (Bl ρ ρ' y))
    (intersection_update_fsHerm_neg_one : τ → Q1 × Q2) (a : τ → K) (ιt : τ → I) (p : I → ℂ) (sR : R → I) (sR' : R' → I)
    (hop : ∀ t ρ ρ', Bl ρ ρ' (X.op t) =
      if intersection_update_fsHerm_neg_one t = (lamR ρ, lamR' ρ') then p ((sR ρ)⁻¹ * ιt t * sR' ρ') • a t else 0)
    (w : Q1 × Q2 → ℝ) (hw0 : ∀ q, 0 < w q)
    (hvec : ∀ t, X.vec t = WithLp.toLp 2 (fun q => if q = intersection_update_fsHerm_neg_one t then ((w q : ℝ) : ℂ) • a t else 0))
    (hio : ∀ t, X.io (X.rowOf t) = ιt t)
    (U : Set I) (h0 : ∀ x, x ∉ U → p x = 0) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x) (hn : ∀ u ∈ U, conj (p u) * p u = 1)
    (hGG : ∀ i j, X.GG i j = conj (gamOf U p (j⁻¹ * i)))
    (A : Q1 → Set I) (A' : Q2 → Set I)
    (hA : ∀ q, Function.Bijective
      (fun x : A q × {ρ // lamR ρ = q} × U => (x.1 : I) * sR x.2.1.1 * (x.2.2 : I)))
    (hA' : ∀ q, Function.Bijective
      (fun x : A' q × {ρ // lamR' ρ = q} × U => (x.1 : I) * sR' x.2.1.1 * (x.2.2 : I)))
    (hwA : ∀ q, w q ^ 2 = ((Nat.card (A q.1) : ℝ) * (Nat.card (A' q.2) : ℝ))⁻¹)
    (hsatL : ∀ q, ∀ b ∈ A q.1, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (b * i)) (Zs S intersection_update_fsHerm_neg_one ιt a q (b * j)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsatR : ∀ q, ∀ b ∈ A' q.2, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (i * b⁻¹)) (Zs S intersection_update_fsHerm_neg_one ιt a q (j * b⁻¹)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsum : Summable fun t => ‖X.op t‖) (hsumv : Summable fun t => ‖X.vec t‖) :
    X.NormExpansionOn S := by
  classical
  set G : Q1 × Q2 → I → I → ℂ := fun q i j => inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j) with hGdef

  have ha_le : ∀ t, w (intersection_update_fsHerm_neg_one t) * ‖a t‖ ≤ ‖X.vec t‖ := by
    intro t
    have e : (X.vec t).ofLp (intersection_update_fsHerm_neg_one t) = ((w (intersection_update_fsHerm_neg_one t) : ℝ) : ℂ) • a t := by
      rw [hvec t, PiLp.toLp_apply, if_pos rfl]
    have h1 := PiLp.norm_apply_le (X.vec t) (intersection_update_fsHerm_neg_one t)
    rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw0 _).le] at h1
    exact h1
  have hsm : ∀ (q : Q1 × Q2) (c : τ → Prop) {dc : DecidablePred c} (z : ℂ), (∀ t, c t → intersection_update_fsHerm_neg_one t = q) →
      Summable (fun t => if c t then z • a t else 0) := by
    intro q c dc z hc
    refine Summable.of_norm_bounded (g := fun t => ‖z‖ * ((w q)⁻¹ * ‖X.vec t‖))
      ((hsumv.mul_left _).mul_left _) ?_
    intro t
    by_cases h : c t
    · rw [if_pos h, norm_smul]
      gcongr
      have := ha_le t
      rw [hc t h] at this
      rw [inv_mul_eq_div, le_div_iff₀ (hw0 q)]
      linarith
    · rw [if_neg h, norm_zero]
      have := hw0 q
      positivity

  have hF : Summable (S.indicator X.op) := (hsum.of_norm).indicator S
  have hBl_part : ∀ ρ ρ', Bl ρ ρ' (X.part S) =
      ∑ i, p ((sR ρ)⁻¹ * i * sR' ρ') • Zs S intersection_update_fsHerm_neg_one ιt a (lamR ρ, lamR' ρ') i := by
    intro ρ ρ'
    unfold Formalism.FourierDecayAlt.PB.Terms.part Zs
    rw [(Bl ρ ρ').map_tsum hF]
    simp_rw [← tsum_const_smul'', smul_ite, smul_zero]
    rw [← Summable.tsum_finsetSum]
    swap
    · intro i _
      exact hsm (lamR ρ, lamR' ρ') _ _ (fun t h => h.2.1)
    refine tsum_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [if_pos ht, hop t ρ ρ']
      by_cases hs : intersection_update_fsHerm_neg_one t = (lamR ρ, lamR' ρ')
      · rw [if_pos hs, Finset.sum_eq_single (ιt t)]
        · rw [if_pos ⟨ht, hs, rfl⟩]
        · intro i _ hi
          exact if_neg (fun h => hi h.2.2.symm)
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun h => hs h.2.1)
    · rw [if_neg ht, map_zero]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => ht h.1)
  have hnorm : ‖X.part S‖ ^ 2 = (∑ ρ, ∑ ρ', fForm p (G (lamR ρ, lamR' ρ')) (sR ρ) (sR' ρ')).re := by
    rw [@norm_sq_eq_re_inner ℂ, hBl]
    simp only [hBl_part, inner_sum_smul, fForm, hGdef]
    rfl

  have hfib : ∀ q1 q2, ∑ ρ : {ρ // lamR ρ = q1}, ∑ ρ' : {ρ' // lamR' ρ' = q2},
      fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) =
        (((w (q1, q2)) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G (q1, q2) i j := by
    intro q1 q2
    have hrw : ∀ (ρ : {ρ // lamR ρ = q1}) (ρ' : {ρ' // lamR' ρ' = q2}),
        fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) = fForm p (G (q1, q2)) (sR ρ.1) (sR' ρ'.1) := by
      intro ρ ρ'; rw [ρ.2, ρ'.2]
    simp_rw [hrw]
    have hc := card_ne_zero_of_bij (A q1) U (fun c : {ρ // lamR ρ = q1} => sR c.1) (hA q1)
    have hc' := card_ne_zero_of_bij (A' q2) U (fun c : {ρ' // lamR' ρ' = q2} => sR' c.1) (hA' q2)
    have ho := orbitSum2 (A q1) (A' q2) U (fun c : {ρ // lamR ρ = q1} => sR c.1)
      (fun c : {ρ' // lamR' ρ' = q2} => sR' c.1) (hA q1) (hA' q2) (fForm p (G (q1, q2)))
      (fun x y b hb v hv => fForm_left U p hl hn _ b (fun i j => hsatL (q1, q2) b hb i j) x y v hv)
      (fun x y b hb v hv => fForm_right U p hr hn _ b (fun i j => hsatR (q1, q2) b hb i j) x y v hv)
    rw [fForm_sum U p h0 hr hn hc.2] at ho
    try beta_reduce at ho
    have hne : ((Nat.card (A q1) : ℂ) * Nat.card U) * ((Nat.card (A' q2) : ℂ) * Nat.card U) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc.1 hc.2) (mul_ne_zero hc'.1 hc'.2)
    have hw2 : (((w (q1, q2)) ^ 2 : ℝ) : ℂ) = ((Nat.card (A q1) : ℂ) * (Nat.card (A' q2) : ℂ))⁻¹ := by
      rw [hwA]; push_cast; ring
    obtain ⟨hA1, hU1⟩ := hc
    obtain ⟨hA2, -⟩ := hc'
    rw [hw2]
    apply mul_left_cancel₀ hne
    rw [← ho]
    field_simp

  have hvp : ∀ i q, (X.vecPart S i).ofLp q = ((w q : ℝ) : ℂ) • Zs S intersection_update_fsHerm_neg_one ιt a q i := by
    intro i q
    unfold Formalism.FourierDecayAlt.PB.Terms.vecPart Zs
    have hs : Summable ((S ∩ {t | X.io (X.rowOf t) = i}).indicator X.vec) := (hsumv.of_norm).indicator _
    have hm := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Q1 × Q2 => K) q).map_tsum hs
    simp only [PiLp.proj_apply] at hm
    rw [hm, ← tsum_const_smul'']
    refine tsum_congr fun t => ?_
    by_cases h1 : t ∈ S <;> by_cases h2 : ιt t = i <;> by_cases h3 : intersection_update_fsHerm_neg_one t = q <;>
      simp [Set.indicator_apply, hvec t, hio t, h1, h2, h3, @eq_comm _ q (intersection_update_fsHerm_neg_one t)]
  have hinner : ∀ i j, inner ℂ (X.vecPart S i) (X.vecPart S j) = ∑ q, (((w q) ^ 2 : ℝ) : ℂ) * G q i j := by
    intro i j
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hvp, hvp, inner_smul_left, inner_smul_right, Complex.conj_ofReal, hGdef]
    push_cast
    ring
  unfold Formalism.FourierDecayAlt.PB.Terms.NormExpansionOn
  rw [hnorm]
  congr 1
  simp_rw [hinner, hGG]
  calc ∑ ρ, ∑ ρ', fForm p (G (lamR ρ, lamR' ρ')) (sR ρ) (sR' ρ')
      = ∑ q1, ∑ ρ : {ρ // lamR ρ = q1}, ∑ q2, ∑ ρ' : {ρ' // lamR' ρ' = q2},
          fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) := by
        rw [← Fintype.sum_fiberwise lamR]
        refine Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun ρ _ => ?_
        exact (Fintype.sum_fiberwise lamR' _).symm
    _ = ∑ q1, ∑ q2, ∑ ρ : {ρ // lamR ρ = q1}, ∑ ρ' : {ρ' // lamR' ρ' = q2},
          fForm p (G (lamR ρ.1, lamR' ρ'.1)) (sR ρ.1) (sR' ρ'.1) := by
        refine Finset.sum_congr rfl fun q1 _ => ?_
        exact Finset.sum_comm
    _ = ∑ q1, ∑ q2, (((w (q1, q2)) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G (q1, q2) i j := by
        refine Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun q2 _ => hfib q1 q2
    _ = ∑ q : Q1 × Q2, (((w q) ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (gamOf U p (i * j⁻¹)) * G q i j :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, conj (gamOf U p (j⁻¹ * i)) * ∑ q, (((w q) ^ 2 : ℝ) : ℂ) * G q i j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
        rw [gamOf_comm U p i j⁻¹]
        ring
end Formalism.L2.SG.NormCut
