-- Prove2me | solution 1 for ConvexSDDP.Stoch.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:44:08.9313+00:00
-- url     : https://prove2.me/submissions/f45a127b-5776-4722-a5e0-a07a01e49a1c

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace Aux_SDDP26

lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

end Aux_SDDP26

open ConvexSDDP.Stoch in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ k n, ¬ IsLeaf T n →
      r.Vc (k + 1) n (r.x k n) = r.θ k n ∧
      (ys k n = true → r.θ k n = ∑ m ∈ T.children n,
        ((M.Φ m / M.Φ n : ℝ) : EReal) * (M.C m (r.x k n) (r.u k m) + r.Vc k m (r.x k m))) := by
  obtain ⟨h0, hleaf, hroot, hchild, hhat, hθβ, hstep⟩ := hr
  have hΦ : ∀ m, 0 < M.Φ m := hH2.1.1
  have hw : ∀ m n : T.Node, (0 : EReal) ≤ ((M.Φ m / M.Φ n : ℝ) : EReal) := fun m n =>
    EReal.coe_nonneg.mpr (div_nonneg (hΦ m).le (hΦ n).le)
  have hch : ∀ n, ∀ m ∈ T.children n, m ≠ T.root ∧ T.anc m = n := by
    intro n m hm
    simp only [Tree.children, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    refine ⟨fun h => ?_, hm.2⟩
    have := T.root_stage
    rw [← h] at this
    omega
  -- monotonicity of the cut models
  have hVmono : ∀ k m y, r.Vc k m y ≤ r.Vc (k + 1) m y := by
    intro k m y
    by_cases hl : IsLeaf T m
    · rw [hleaf k m hl, hleaf (k + 1) m hl]
    · rw [hstep k m hl]; exact le_max_left _ _
  let S : ℕ → T.Node → EuclideanSpace ℝ (Fin d) → EReal := fun k n y =>
    ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
      ⨅ v ∈ M.Ut m y, (M.C m y v + r.Vc k m (M.f m (y, v)))
  have hSmono : ∀ k n y, S k n y ≤ S (k + 1) n y := by
    intro k n y
    apply Finset.sum_le_sum
    intro m _
    apply mul_le_mul_of_nonneg_left _ (hw m n)
    exact iInf₂_mono (fun v _ => add_le_add le_rfl (hVmono k m _))
  -- invariant
  have inv : ∀ k n, ¬ IsLeaf T n → ∀ y ∈ affineSpan ℝ (M.X n), r.Vc k n y ≤ S k n y := by
    intro k
    induction k with
    | zero =>
      intro n hn y _
      rw [h0 n hn]
      exact bot_le
    | succ k ih =>
      intro n hn y hy
      rw [hstep k n hn]
      apply max_le
      · exact le_trans (ih n hn y hy) (hSmono k n y)
      · cases hys : ys k n
        · obtain ⟨-, -, hcut⟩ := (hθβ k n hn).2 hys
          exact le_trans (hcut y) (le_trans (ih n hn y hy) (hSmono k n y))
        · obtain ⟨hθ, hβ⟩ := (hθβ k n hn).1 hys
          rw [hθ, hβ]
          have hsum : (∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * r.θhat k m) +
              ((inner ℝ (∑ m ∈ T.children n, (M.Φ m / M.Φ n) • r.βhat k m) (y - r.x k n) : ℝ) :
                EReal) =
              ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
                (r.θhat k m + ((inner ℝ (r.βhat k m) (y - r.x k n) : ℝ) : EReal)) := by
            rw [sum_inner, Aux_SDDP26.coe_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [EReal.left_distrib_of_nonneg_of_ne_top (hw m n) (EReal.coe_ne_top _),
              real_inner_smul_left, EReal.coe_mul]
          rw [hsum]
          refine le_trans ?_ (hSmono k n y)
          apply Finset.sum_le_sum
          intro m hm
          apply mul_le_mul_of_nonneg_left _ (hw m n)
          obtain ⟨hmr, hanc⟩ := hch n m hm
          have := (hhat k m hmr (by rw [hanc]; exact hys)).2.2.2 y (by rw [hanc]; exact hy)
          rw [hanc] at this
          exact this
  -- the trial point lies in X n
  have hxX : ∀ k n, r.x k n ∈ M.X n := by
    intro k n
    by_cases hn : n = T.root
    · subst hn; rw [hroot k]; exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := hchild k n hn
      rw [hx]; exact hu.2
  intro k n hn
  have hθhat : ys k n = true → ∀ m ∈ T.children n,
      r.θhat k m = M.C m (r.x k n) (r.u k m) + r.Vc k m (r.x k m) := by
    intro hys m hm
    obtain ⟨hmr, hanc⟩ := hch n m hm
    have := (hhat k m hmr (by rw [hanc]; exact hys)).1
    rw [hanc] at this
    exact this
  refine ⟨?_, fun hys => ?_⟩
  · rw [hstep k n hn]
    simp only [sub_self, inner_zero_right, EReal.coe_zero, add_zero]
    apply max_eq_right
    cases hys : ys k n
    · rw [((hθβ k n hn).2 hys).1]
    · rw [((hθβ k n hn).1 hys).1]
      refine le_trans (inv k n hn (r.x k n) (subset_affineSpan ℝ _ (hxX k n))) ?_
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (hw m n)
      obtain ⟨hmr, hanc⟩ := hch n m hm
      obtain ⟨-, hu, -, hx⟩ := hchild k m hmr
      rw [hanc] at hu hx
      rw [hθhat hys m hm, hx]
      exact biInf_le (fun v => M.C m (r.x k n) v + r.Vc k m (M.f m (r.x k n, v))) hu
  · rw [((hθβ k n hn).1 hys).1]
    exact Finset.sum_congr rfl (fun m hm => by rw [hθhat hys m hm])
