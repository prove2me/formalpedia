-- Prove2me | solution 1 for BayesGroupHard.VertexCover.Supplement.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:30.062903+00:00
-- url     : https://prove2.me/submissions/6d4afa2e-26dc-4abf-ad38-2c8160d07a17

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

open BayesGroupHard
open BayesGroupHard.VertexCover
open BayesGroupHard.VertexCover.Supplement

open Finset

/-- (20), p. 32: in the Appendix B network, every element agent reports `µ_ε,0(1) = 1/2` at time
zero; at time one her log-belief ratio is `φ_ε,1 = (ℓ_1 - ℓ_0)(2 s_κ + Σ_j s_ε(j)) + 5 ℓ_0`;
she reports `243/371` (that is, `φ_ε,1 = 3ℓ_1 + 2ℓ_0`, (19)) iff `2 s_κ + Σ_j s_ε(j) = 3`; and
the history (19) holds iff the informative signals lie in `Σ`. -/
theorem solution {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool) :
    (∀ e, report (xcNet X) 0 (epsilon e) s = 1 / 2) ∧
    (∀ e, rLog (xcNet X) 1 (epsilon e) s =
      (ellOne - ellZero) *
        ((2 * bit (s kappa) +
          ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) : ℕ) : ℝ) +
        5 * ellZero) ∧
    (∀ e, report (xcNet X) 1 (epsilon e) s = 243 / 371 ↔
      2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) = 3) ∧
    (Observed X s ↔ project s ∈ sigma X) := by
      classical
      have key : ∀ (N : BinNet (XAgent n)) (θ : Bool) (A : Finset (XAgent n))
          (s : XAgent n → Bool) (I : Finset (XAgent n → Bool)),
          (∀ s', s' ∈ I ↔ ∀ k ∈ A, s' k = s k) →
          ∑ s' ∈ I, jointProb N θ s' = ∏ k ∈ A, sig N k θ (s k) := by
        intro N θ A s I hI
        have hIe : I = univ.filter (fun s' : XAgent n → Bool => ∀ k ∈ A, s' k = s k) := by
          ext s'; simp [hI]
        rw [hIe, Finset.sum_filter]
        have h1 : ∀ s' : XAgent n → Bool, (if ∀ k ∈ A, s' k = s k then jointProb N θ s' else 0) =
            ∏ k, (if k ∈ A then (if s' k = s k then sig N k θ (s' k) else 0)
              else sig N k θ (s' k)) := by
          intro s'
          unfold jointProb
          split_ifs with h
          · refine Finset.prod_congr rfl (fun k _ => ?_)
            by_cases hk : k ∈ A
            · simp [hk, h k hk]
            · simp [hk]
          · push Not at h
            obtain ⟨k, hk, hne⟩ := h
            exact (Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk, hne])).symm
        simp_rw [h1]
        rw [← Fintype.prod_sum (f := fun k b => if k ∈ A then (if b = s k then sig N k θ b else 0)
              else sig N k θ b)]
        have h2 : ∀ k, (∑ b : Bool, (if k ∈ A then (if b = s k then sig N k θ b else 0)
              else sig N k θ b)) = if k ∈ A then sig N k θ (s k) else 1 := by
          intro k
          rw [Fintype.sum_bool]
          by_cases hk : k ∈ A
          · cases h : s k <;> simp [hk]
          · simp [hk, sig]
        simp_rw [h2]
        rw [Finset.prod_ite_mem, Finset.univ_inter]
      have hpost : ∀ (N : BinNet (XAgent n)) (θ : Bool) (A : Finset (XAgent n))
          (s : XAgent n → Bool) (I : Finset (XAgent n → Bool)),
          (∀ s', s' ∈ I ↔ ∀ k ∈ A, s' k = s k) →
          post N θ I = (∏ k ∈ A, sig N k θ (s k)) /
            ((∏ k ∈ A, sig N k true (s k)) + ∏ k ∈ A, sig N k false (s k)) := by
        intro N θ A s I hI
        unfold post
        rw [Fintype.sum_bool, key N θ A s I hI, key N true A s I hI, key N false A s I hI,
          ← mul_add, mul_div_mul_left _ _ (by norm_num)]
      have hrep0 : ∀ (N : BinNet (XAgent n)) (j : XAgent n) (s : XAgent n → Bool),
          report N 0 j s = sig N j true (s j) / (sig N j true (s j) + sig N j false (s j)) := by
        intro N j s
        unfold report belief rInfo
        rw [hpost N true {j} s]
        · simp
        · intro s'
          unfold rInfoUsing
          simp
      set N := xcNet X with hN
      have hsig : ∀ k θ b, 0 < sig N k θ b := by
        intro k θ b
        rcases k with j | e | b'
        · cases θ <;> cases b <;> simp [sig, N, xcNet] <;> norm_num
        · cases θ <;> cases b <;> simp [sig, N, xcNet] <;> norm_num
        · cases b' <;> cases θ <;> cases b <;> simp [sig, N, xcNet] <;> norm_num
      have h1 : ∀ e, report N 0 (epsilon e) s = 1 / 2 := by
        intro e
        rw [hrep0]
        cases s (epsilon e) <;> simp [sig, N, xcNet, epsilon] <;> norm_num
      have hinj : ∀ j, (∀ e, j ≠ epsilon e) → j ≠ observer → ∀ s s' : XAgent n → Bool,
          report N 0 j s' = report N 0 j s ↔ s' j = s j := by
        intro j hj ho s s'
        rw [hrep0, hrep0]
        rcases j with j | e | b'
        · cases s (Sum.inl j) <;> cases s' (Sum.inl j) <;> simp [sig, N, xcNet] <;> norm_num
        · exact absurd rfl (hj e)
        · cases b'
          · cases s (Sum.inr (Sum.inr false)) <;> cases s' (Sum.inr (Sum.inr false)) <;>
              simp [sig, N, xcNet] <;> norm_num
          · exact absurd rfl ho
      have hI1 : ∀ e s', s' ∈ rInfo N 1 (epsilon e) s ↔ ∀ k ∈ N.nbr (epsilon e), s' k = s k := by
        intro e s'
        unfold rInfo rInfoUsing
        simp only [mem_filter, mem_univ, true_and, Nat.lt_one_iff, forall_eq]
        have hr : ∀ j (t : XAgent n → Bool), reportsUpTo N 1 0 j t = report N 0 j t := fun _ _ => rfl
        simp only [hr]
        constructor
        · rintro ⟨hs, h⟩ k hk
          by_cases hke : k = epsilon e
          · subst hke; exact hs
          · have hk' : k = kappa ∨ ∃ j, k = tau j := by
              have : k ∈ insert (epsilon e) (insert kappa
                  ((univ.filter (fun j => e ∈ X.sets j)).image tau)) := hk
              simp only [mem_insert, mem_image] at this
              rcases this with h | h | ⟨j, _, hj⟩
              · exact absurd h hke
              · exact Or.inl h
              · exact Or.inr ⟨j, hj.symm⟩
            rcases hk' with rfl | ⟨j, rfl⟩
            · exact (hinj kappa (fun e' => by simp [kappa, epsilon]) (by simp [kappa, observer])
                s s').1 (h _ hk)
            · exact (hinj (tau j) (fun e' => by simp [tau, epsilon]) (by simp [tau, observer])
                s s').1 (h _ hk)
        · intro h
          refine ⟨h _ (N.self_mem _), fun k hk => ?_⟩
          rw [hrep0, hrep0, h k hk]
      have hW : ∀ e θ, ∏ k ∈ N.nbr (epsilon e), sig N k θ (s k) =
          sig N (epsilon e) θ (s (epsilon e)) * (sig N kappa θ (s kappa) *
            ∏ j ∈ univ.filter (fun j => e ∈ X.sets j), sig N (tau j) θ (s (tau j))) := by
        intro e θ
        change ∏ k ∈ insert (epsilon e) (insert kappa
            ((univ.filter (fun j => e ∈ X.sets j)).image tau)), sig N k θ (s k) = _
        rw [prod_insert, prod_insert, prod_image]
        · intro a _ b _ h; simpa [tau] using h
        · simp [kappa, tau]
        · simp [epsilon, kappa, tau]
      have hε : ∀ e b, sig N (epsilon e) true b = sig N (epsilon e) false b := by
        intro e b; simp [sig, N, xcNet, epsilon]
      have hκ : sig N kappa true (s kappa) / sig N kappa false (s kappa) =
          9 / 16 * 2 ^ (2 * bit (s kappa)) := by
        cases s kappa <;> simp [sig, N, xcNet, kappa, bit] <;> norm_num
      have hτ : ∀ j, sig N (tau j) true (s (tau j)) / sig N (tau j) false (s (tau j)) =
          3 / 4 * 2 ^ (bit (s (tau j))) := by
        intro j
        cases s (tau j) <;> simp [sig, N, xcNet, tau, bit] <;> norm_num
      have hR : ∀ e, (∏ k ∈ N.nbr (epsilon e), sig N k true (s k)) /
          (∏ k ∈ N.nbr (epsilon e), sig N k false (s k)) =
          (3 / 4) ^ 5 * 2 ^ (2 * bit (s kappa) +
              ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j))) := by
        intro e
        rw [hW, hW, hε, mul_div_mul_left _ _ (ne_of_gt (hsig _ _ _)), mul_div_mul_comm,
          ← prod_div_distrib, hκ, Finset.prod_congr rfl (fun j _ => hτ j), prod_mul_distrib,
          prod_const, X.regular e, prod_pow_eq_pow_sum, pow_add]
        ring
      have hpos : ∀ e θ, 0 < ∏ k ∈ N.nbr (epsilon e), sig N k θ (s k) :=
        fun e θ => prod_pos (fun k _ => hsig _ _ _)
      have hb : ∀ e θ, belief N 1 (epsilon e) s θ =
          (∏ k ∈ N.nbr (epsilon e), sig N k θ (s k)) /
            ((∏ k ∈ N.nbr (epsilon e), sig N k true (s k)) +
              ∏ k ∈ N.nbr (epsilon e), sig N k false (s k)) := by
        intro e θ
        unfold belief
        exact hpost N θ _ s _ (hI1 e)
      have h2 : ∀ e, rLog N 1 (epsilon e) s =
          (ellOne - ellZero) *
            ((2 * bit (s kappa) +
              ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) : ℕ) : ℝ) +
            5 * ellZero := by
        intro e
        unfold rLog
        rw [hb, hb, div_div_div_cancel_right₀ (ne_of_gt (add_pos (hpos e true) (hpos e false))),
          hR, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
        have hl0 : ellZero = Real.log (3 / 4) := by unfold ellZero; norm_num
        have hl1 : ellOne = Real.log (3 / 4) + Real.log 2 := by
          unfold ellOne
          rw [← Real.log_mul (by norm_num) (by norm_num)]
          norm_num
        rw [hl0, hl1]
        ring
      have h3 : ∀ e, report N 1 (epsilon e) s = 243 / 371 ↔
          2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)) = 3 := by
        intro e
        have hrep : report N 1 (epsilon e) s =
            ((3 / 4) ^ 5 * 2 ^ (2 * bit (s kappa) +
              ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j)))) /
            ((3 / 4) ^ 5 * 2 ^ (2 * bit (s kappa) +
              ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j))) + 1) := by
          unfold report
          rw [hb, ← hR]
          have := hpos e false
          field_simp
        rw [hrep]
        set k := 2 * bit (s kappa) + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s (tau j))
        have hk0 : (0 : ℝ) < (3 / 4) ^ 5 * 2 ^ k := by positivity
        rw [div_eq_div_iff (by positivity) (by norm_num)]
        constructor
        · intro h
          have h8 : (2 : ℝ) ^ k = 2 ^ 3 := by nlinarith
          exact (pow_right_inj₀ (by norm_num) (by norm_num)).1 h8
        · intro h
          rw [h]; norm_num
      refine ⟨h1, h2, h3, ?_⟩
      unfold Observed
      simp only [sigma, project, mem_filter, mem_univ, true_and]
      constructor
      · intro h e; exact (h3 e).1 (h e).2
      · intro h e; exact ⟨h1 e, (h3 e).2 (h e)⟩
