-- Prove2me | solution 1 for ConvexRMDP.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:27:43.967295+00:00
-- url     : https://prove2.me/submissions/b292ca9d-5565-4e46-ac96-d028dcf6c36c

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace Aux_CRl42

variable {S : Type*} [Fintype S]

theorem amgm (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s) :
    ∏ s, u s ^ (γ * p s) ≤ ∑ s, γ * p s * u s + (1 - γ) := by
  have h := Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset (Option S)))
    (fun o : Option S => o.elim (1 - γ) (fun s => γ * p s)) (fun o => o.elim 1 u)
    (by
      intro o _
      cases o with
      | none => simp; linarith
      | some s => simp; exact mul_nonneg hγ0 (hp s))
    (by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some]
      rw [← Finset.mul_sum, hp1]; ring)
    (by
      intro o _
      cases o with
      | none => simp
      | some s => simp; exact hu s)
  rw [Fintype.prod_option, Fintype.sum_option] at h
  simp only [Option.elim_none, Option.elim_some, Real.one_rpow, one_mul, mul_one] at h
  linarith

noncomputable def F (γ : ℝ) (p x : S → ℝ) : ℝ := ∏ s, x s ^ (γ * p s)

theorem F_nonneg (γ : ℝ) (p x : S → ℝ) (hx : ∀ s, 0 < x s) : 0 ≤ F γ p x :=
  Finset.prod_nonneg (fun s _ => Real.rpow_nonneg (hx s).le _)

theorem conc (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (x y : S → ℝ) (hx : ∀ s, 0 < x s) (hy : ∀ s, 0 < y s)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * F γ p x + b * F γ p y ≤ F γ p (a • x + b • y) := by
  set z := a • x + b • y with hzdef
  have hz : ∀ s, 0 < z s := by
    intro s
    simp only [hzdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with h | h
    · rw [← h] at hab ⊢; simp at hab; rw [hab]; simp [hy s]
    · nlinarith [hx s, hy s]
  have hFz : 0 < F γ p z := Finset.prod_pos (fun s _ => Real.rpow_pos_of_pos (hz s) _)
  have hratio : ∀ u : S → ℝ, (∀ s, 0 < u s) →
      F γ p u = F γ p z * ∏ s, (u s / z s) ^ (γ * p s) := by
    intro u hu
    unfold F
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    rw [Real.div_rpow (hu s).le (hz s).le, mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos (hz s) _).ne'
  have hrx := amgm γ hγ0 hγ1 p hp hp1 (fun s => x s / z s) (fun s => (div_pos (hx s) (hz s)).le)
  have hry := amgm γ hγ0 hγ1 p hp hp1 (fun s => y s / z s) (fun s => (div_pos (hy s) (hz s)).le)
  rw [hratio x hx, hratio y hy]
  have hsum : a * (∑ s, γ * p s * (x s / z s) + (1 - γ)) +
      b * (∑ s, γ * p s * (y s / z s) + (1 - γ)) = 1 := by
    have : ∀ s, a * (γ * p s * (x s / z s)) + b * (γ * p s * (y s / z s)) = γ * p s := by
      intro s
      have hzs : z s = a * x s + b * y s := by simp [hzdef]
      have hz0 := (hz s).ne'
      rw [show a * (γ * p s * (x s / z s)) + b * (γ * p s * (y s / z s)) =
        γ * p s * ((a * x s + b * y s) / z s) by ring, ← hzs, div_self hz0, mul_one]
    calc a * (∑ s, γ * p s * (x s / z s) + (1 - γ)) + b * (∑ s, γ * p s * (y s / z s) + (1 - γ))
        = ∑ s, (a * (γ * p s * (x s / z s)) + b * (γ * p s * (y s / z s))) + (a + b) * (1 - γ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
      _ = 1 := by
          simp only [this]
          rw [← Finset.mul_sum, hp1, hab]; ring
  have h1 := mul_le_mul_of_nonneg_left hrx (mul_nonneg ha hFz.le)
  have h2 := mul_le_mul_of_nonneg_left hry (mul_nonneg hb hFz.le)
  nlinarith

end Aux_CRl42

open ConvexRMDP Aux_CRl42 in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (s : S) :
    ConcaveOn ℝ (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) (fun x => M.tOp b x s) := by
  have hγ0 := M.γ_pos.le
  have hγ1 := M.γ_lt_one.le
  refine ⟨convex_pi (fun _ _ => convex_Ioi 0), ?_⟩
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies] at hx hy
  simp only [smul_eq_mul]
  unfold RMDP.tOp
  have hG : ∀ a' : A,
      a * sInf ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a') +
        c * sInf ((fun p : S → ℝ => ∏ s', y s' ^ (M.γ * p s')) '' M.U s a') ≤
      sInf ((fun p : S → ℝ => ∏ s', (a • x + c • y) s' ^ (M.γ * p s')) '' M.U s a') := by
    intro a'
    apply le_csInf ((M.U_nonempty s a').image _)
    rintro v ⟨p, hpU, rfl⟩
    have hpS := M.U_subset s a' hpU
    have hp0 : ∀ s', 0 ≤ p s' := hpS.1
    have hp1 : ∑ s', p s' = 1 := hpS.2
    have hbx : BddBelow ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a') :=
      ⟨0, by rintro _ ⟨q, _, rfl⟩; exact F_nonneg M.γ q x hx⟩
    have hby : BddBelow ((fun p : S → ℝ => ∏ s', y s' ^ (M.γ * p s')) '' M.U s a') :=
      ⟨0, by rintro _ ⟨q, _, rfl⟩; exact F_nonneg M.γ q y hy⟩
    have h1 := csInf_le hbx ⟨p, hpU, rfl⟩
    have h2 := csInf_le hby ⟨p, hpU, rfl⟩
    have h3 := conc M.γ hγ0 hγ1 p hp0 hp1 x y hx hy a c ha hc hac
    unfold F at h3
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hc]
  have hω : ∀ a' : A, 0 ≤ M.omega b s a' := by
    intro a'; unfold RMDP.omega expB; positivity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a' _
  have := mul_le_mul_of_nonneg_left (hG a') (hω a')
  nlinarith
