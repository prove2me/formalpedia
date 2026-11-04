-- Prove2me | solution 1 for ConvexSDDP.Stoch.lemma_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:52:27.4032+00:00
-- url     : https://prove2.me/submissions/8bfb6d68-4328-49f9-b5fa-7730985ab32a

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
open StochasticProg.Multistage Filter Topology

namespace Aux_SDDP31ii

lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

end Aux_SDDP31ii

open ConvexSDDP.Stoch in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ k n, ¬ IsLeaf T n →
      (∀ y ∈ affineSpan ℝ (M.X n), r.Vc k n y ≤ M.Vtilde n y) ∧
      ∀ y, M.Vtilde n y ≤ M.V n y := by
  classical
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
  -- the fuel recursion is antitone in the fuel
  have hanti : ∀ h n z, M.Vfuel (h + 1) n z ≤ M.Vfuel h n z := by
    intro h
    induction h with
    | zero =>
      intro n z
      have e : M.Vfuel 0 n z = ⊤ := rfl
      rw [e]
      exact le_top
    | succ h ih =>
      intro n z
      simp only [Model.Vfuel]
      split_ifs
      · exact le_rfl
      · apply Finset.sum_le_sum
        intro m _
        apply mul_le_mul_of_nonneg_left _ (hw m n)
        exact iInf₂_mono (fun v _ => add_le_add le_rfl (ih m _))
      · exact le_rfl
  have hanti' : ∀ h h', h ≤ h' → ∀ n z, M.Vfuel h' n z ≤ M.Vfuel h n z := by
    intro h h' hhh' n z
    induction hhh' with
    | refl => exact le_rfl
    | step _ ih => exact (hanti _ n z).trans ih
  have hout : ∀ h m z, z ∉ M.X m → M.Vfuel h m z = ⊤ := by
    intro h m z hz
    cases h with
    | zero => rfl
    | succ h => simp [Model.Vfuel, hz]
  have hcard : Fintype.card T.Node = (Fintype.card T.Node - 1) + 1 := by
    have : 0 < Fintype.card T.Node := Fintype.card_pos_iff.mpr ⟨T.root⟩
    omega
  -- Ṽ ≤ V
  have hVtV : ∀ n, ¬ IsLeaf T n → ∀ y, M.Vtilde n y ≤ M.V n y := by
    intro n hn y
    have eV : M.V n y = M.Vfuel ((Fintype.card T.Node - 1) + 1) n y := by
      unfold Model.V; rw [← hcard]
    rw [eV]
    by_cases hy : y ∈ M.X n
    · simp only [Model.Vfuel, hy, hn, if_true, if_false]
      unfold Model.Vtilde
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (hw m n)
      apply le_iInf₂
      intro u hu
      by_cases hf : M.f m (y, u) ∈ M.X m
      · refine (biInf_le (fun v => M.W m y v) (show u ∈ M.Ut m y from ⟨hu, hf⟩)).trans ?_
        unfold Model.W
        apply add_le_add le_rfl
        unfold Model.V
        exact hanti' _ _ (by omega) m _
      · rw [hout _ m _ hf, EReal.add_top_of_ne_bot]
        · exact le_top
        · exact (hH2.2.2.2.2.1 m (hch n m hm).1).1.1 (y, u)
    · simp only [Model.Vfuel, hy, if_false]
      exact le_top
  -- leaves: Vc = V
  have hVleaf : ∀ k m y, IsLeaf T m → r.Vc k m y ≤ M.V m y := by
    intro k m y hm
    rw [hleaf k m hm]
  -- main induction on k
  have main : ∀ k, (∀ n, ¬ IsLeaf T n → ∀ y ∈ affineSpan ℝ (M.X n), r.Vc k n y ≤ M.Vtilde n y) := by
    intro k
    induction k with
    | zero =>
      intro n hn y _
      rw [h0 n hn]
      exact bot_le
    | succ k ih =>
      -- Vc k ≤ V on X for every node
      have hVcV : ∀ m, ∀ z ∈ M.X m, r.Vc k m z ≤ M.V m z := by
        intro m z hz
        by_cases hm : IsLeaf T m
        · exact hVleaf k m z hm
        · exact (ih m hm z (subset_affineSpan ℝ _ hz)).trans (hVtV m hm z)
      intro n hn y hy
      rw [hstep k n hn]
      apply max_le (ih n hn y hy)
      cases hys : ys k n
      · obtain ⟨-, -, hcut⟩ := (hθβ k n hn).2 hys
        exact le_trans (hcut y) (ih n hn y hy)
      · obtain ⟨hθ, hβ⟩ := (hθβ k n hn).1 hys
        rw [hθ, hβ]
        have hsum : (∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * r.θhat k m) +
            ((inner ℝ (∑ m ∈ T.children n, (M.Φ m / M.Φ n) • r.βhat k m) (y - r.x k n) : ℝ) :
              EReal) =
            ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
              (r.θhat k m + ((inner ℝ (r.βhat k m) (y - r.x k n) : ℝ) : EReal)) := by
          rw [sum_inner, Aux_SDDP31ii.coe_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [EReal.left_distrib_of_nonneg_of_ne_top (hw m n) (EReal.coe_ne_top _),
            real_inner_smul_left, EReal.coe_mul]
        rw [hsum]
        unfold Model.Vtilde
        apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_left _ (hw m n)
        obtain ⟨hmr, hanc⟩ := hch n m hm
        have := (hhat k m hmr (by rw [hanc]; exact hys)).2.2.2 y (by rw [hanc]; exact hy)
        rw [hanc] at this
        refine this.trans (iInf₂_mono (fun v hv => ?_))
        unfold Model.W
        exact add_le_add le_rfl (hVcV m _ hv.2)
  intro k n hn
  exact ⟨main k n hn, hVtV n hn⟩
