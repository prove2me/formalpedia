-- Prove2me | solution 1 for ContJRP.Align.corollary_2_6_scaling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:15:32.638204+00:00
-- url     : https://prove2.me/submissions/202b5df2-80cd-444a-a68c-de93308b3323

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

open ContJRP.Align
open Classical

/-- For commensurable positive `x, y`, `alignMult x y · x = alignMult y x · y` (both sides are the
least common multiple). -/
theorem jrp26_alignMult (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℝ) * x = b * y) :
    (alignMult x y : ℝ) * x = (alignMult y x : ℝ) * y := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hne1 : {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}.Nonempty :=
    ⟨a, ha, b, hb, hab⟩
  have hne2 : {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}.Nonempty :=
    ⟨b, hb, a, ha, hab.symm⟩
  have h1 := Nat.sInf_mem hne1
  have h2 := Nat.sInf_mem hne2
  unfold alignMult
  set a0 := sInf {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}
  set b0 := sInf {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}
  obtain ⟨-, b1, hb1, e1⟩ := h1
  obtain ⟨-, a1, ha1, e2⟩ := h2
  have hle1 : a0 ≤ a1 := Nat.sInf_le ⟨ha1, b0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e2; simp at e2; rcases e2 with e2 | e2 <;> [omega; linarith]), e2.symm⟩
  have hle2 : b0 ≤ b1 := Nat.sInf_le ⟨hb1, a0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e1; simp at e1; rcases e1 with e1 | e1 <;> [omega; linarith]), e1.symm⟩
  have i1 : (a0 : ℝ) * x ≤ (b0 : ℝ) * y := by
    rw [e2]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle1) hx.le
  have i2 : (b0 : ℝ) * y ≤ (a0 : ℝ) * x := by
    rw [e1]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle2) hy.le
  linarith

theorem jrp26_alignMult_pos (x y : ℝ) (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℝ) * x = b * y) :
    0 < alignMult x y := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hne : {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}.Nonempty :=
    ⟨a, ha, b, hb, hab⟩
  exact (Nat.sInf_mem hne).1

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R → ∀ C ∈ components ε Tt Tstar Rstar,
      ∃ γ : ℝ, 1 - ε ≤ γ ∧ γ ≤ 1 + ε ∧ ∀ ℓ ∈ C, R ℓ = γ * Rstar ℓ := by
  intro R hfeas C hC
  have hpos : ∀ ℓ ∈ active ε Tt Tstar, 0 < Rstar ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, -⟩ := hR ℓ hℓ
    rw [hi]; exact hTstar i
  -- the edge relation, unfolded
  have hadj : ∀ b c, (alignGraph ε Tt Tstar Rstar).Adj b c →
      b ∈ active ε Tt Tstar ∧ c ∈ active ε Tt Tstar ∧
        ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * Rstar b = q * Rstar c := by
    intro b c h
    unfold alignGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨-, hr | hr⟩ := h
    · obtain ⟨h1, h2, a, b', ha, -, hb, -, hab⟩ := hr
      exact ⟨h1, h2, a, b', ha, hb, hab⟩
    · obtain ⟨h1, h2, a, b', ha, -, hb, -, hab⟩ := hr
      exact ⟨h2, h1, b', a, hb, ha, hab.symm⟩
  unfold components at hC
  obtain ⟨ℓ0, hℓ0, rfl⟩ := Finset.mem_image.mp hC
  have hR0 := hpos ℓ0 hℓ0
  set γ := R ℓ0 / Rstar ℓ0 with hγ
  obtain ⟨i0, hi0, hseg0⟩ := hR ℓ0 hℓ0
  have hA := hfeas.1 ℓ0 hℓ0
  unfold seg at hseg0
  unfold segClosed at hA
  set a := (1 + ε) ^ ℓ0 * Tt with ha
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  have hTt_pos : 0 < Tt := by
    have : 0 < (1 - ε / 2) * tmin Tstar := mul_pos (by linarith) htmin_pos
    linarith
  have hapos : 0 < a := by
    have : 0 < 1 + ε := by linarith
    positivity
  have hpow : (1 + ε) ^ (ℓ0 + 1) * Tt = (1 + ε) * a := by rw [ha]; ring
  rw [hpow] at hseg0 hA
  rw [← hi0] at hseg0
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [hγ, le_div_iff₀ hR0]
    have h1 : (1 - ε) * Rstar ℓ0 ≤ (1 - ε) * ((1 + ε) * a) :=
      mul_le_mul_of_nonneg_left hseg0.2.le (by linarith)
    have h2 : (1 - ε) * ((1 + ε) * a) ≤ a := by nlinarith [sq_nonneg ε, hapos]
    linarith [hA.1]
  · rw [hγ, div_le_iff₀ hR0]
    have h1 : (1 + ε) * a ≤ (1 + ε) * Rstar ℓ0 :=
      mul_le_mul_of_nonneg_left hseg0.1 (by linarith)
    linarith [hA.2]
  · intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    obtain ⟨hℓa, hreach⟩ := hℓ
    have key : ∀ c, Relation.ReflTransGen (alignGraph ε Tt Tstar Rstar).Adj ℓ0 c →
        R c = γ * Rstar c := by
      intro c hc
      induction hc with
      | refl => rw [hγ]; field_simp
      | tail hb hbc ih =>
        rename_i b c
        obtain ⟨hba, hca, p, q, hp, hq, hpq⟩ := hadj b c hbc
        have hB := hfeas.2 b hba c hca hbc
        have hBs := jrp26_alignMult (Rstar b) (Rstar c) (hpos b hba) (hpos c hca)
          ⟨p, q, hp, hq, hpq⟩
        have hpos2 : (0 : ℝ) < alignMult (Rstar c) (Rstar b) := by
          exact_mod_cast jrp26_alignMult_pos (Rstar c) (Rstar b) ⟨q, p, hq, hp, hpq.symm⟩
        rw [ih] at hB
        have : (alignMult (Rstar c) (Rstar b) : ℝ) * R c =
            (alignMult (Rstar c) (Rstar b) : ℝ) * (γ * Rstar c) := by
          rw [← hB]
          calc (alignMult (Rstar b) (Rstar c) : ℝ) * (γ * Rstar b)
              = γ * ((alignMult (Rstar b) (Rstar c) : ℝ) * Rstar b) := by ring
            _ = γ * ((alignMult (Rstar c) (Rstar b) : ℝ) * Rstar c) := by rw [hBs]
            _ = (alignMult (Rstar c) (Rstar b) : ℝ) * (γ * Rstar c) := by ring
        exact mul_left_cancel₀ hpos2.ne' this
    exact key ℓ ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hreach)
