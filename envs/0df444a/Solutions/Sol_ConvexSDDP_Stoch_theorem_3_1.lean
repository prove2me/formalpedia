-- Prove2me | solution 1 for ConvexSDDP.Stoch.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:41:32.015846+00:00
-- url     : https://prove2.me/submissions/39590c96-0793-4e01-ad9e-f5b7fb9e6312

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_2
import Theorems.Thm_ConvexSDDP_Stoch_eq_32
import Theorems.Thm_ConvexSDDP_Stoch_theorem_3_1_unselected
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology
open ConvexSDDP.Stoch

theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω)) :
    ∀ᵐ ω ∂P,
      (∀ n, ¬ IsLeaf T n →
        Tendsto (fun k => (∑ m ∈ T.children n,
            ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m ((r ω).x (k * τ) n) ((r ω).u (k * τ) m)) -
            M.V n ((r ω).x (k * τ) n)) atTop (𝓝 0)) ∧
      (∀ n, Tendsto
        (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
        atTop (𝓝 0)) := by
  classical
  have hτ : 0 < τ := hadm.1
  -- stocks stay in the constraint sets
  have hxX : ∀ ω k n, (r ω).x k n ∈ M.X n := by
    intro ω k n
    by_cases hroot : n = T.root
    · subst hroot
      rw [(hr ω).2.2.1 k]
      exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := (hr ω).2.2.2.1 k n hroot
      rw [hx]
      exact hu.2
  -- the gap at a leaf is zero
  have hleaf : ∀ n, IsLeaf T n → ∀ ω k,
      M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n) = 0 := by
    intro n hn ω k
    rw [(hr ω).2.1 (k * τ + 1) n hn]
    have hx := hxX ω (k * τ) n
    have hcard : Fintype.card T.Node = (Fintype.card T.Node - 1) + 1 := by
      have : 0 < Fintype.card T.Node := Fintype.card_pos_iff.mpr ⟨n⟩
      omega
    have hV : M.V n ((r ω).x (k * τ) n) = M.VL n ((r ω).x (k * τ) n) := by
      unfold Model.V
      rw [hcard]
      simp [Model.Vfuel, hx, hn]
    rw [hV]
    have h1 := ((hH2.2.2.2.2.2.2.1 n hn).1 _ hx)
    have h2 := (hH2.2.2.2.2.2.1 n hn).1.1 ((r ω).x (k * τ) n)
    exact EReal.sub_self h1 h2
  -- backward induction on the stage
  have key : ∀ s : ℕ, ∀ n : T.Node, H - (T.stage n).val ≤ s → ∀ᵐ ω ∂P,
      Tendsto (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
        atTop (𝓝 0) := by
    intro s
    induction s with
    | zero =>
      intro n hs
      have := (T.stage n).isLt
      omega
    | succ s ih =>
      intro n hs
      by_cases hn : IsLeaf T n
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        simp only [hleaf n hn ω]
        exact tendsto_const_nhds
      · have hch : ∀ᵐ ω ∂P, ∀ m ∈ T.children n,
            Tendsto (fun k => M.V m ((r ω).x (k * τ) m) -
              (r ω).Vc (k * τ + 1) m ((r ω).x (k * τ) m)) atTop (𝓝 0) := by
          have : ∀ m : T.Node, ∀ᵐ ω ∂P, m ∈ T.children n →
              Tendsto (fun k => M.V m ((r ω).x (k * τ) m) -
                (r ω).Vc (k * τ + 1) m ((r ω).x (k * τ) m)) atTop (𝓝 0) := by
            intro m
            by_cases hm : m ∈ T.children n
            · have hst : (T.stage m).val = (T.stage n).val + 1 := by
                simp [Tree.children] at hm
                exact hm.1
              have hlt := (T.stage m).isLt
              filter_upwards [ih m (by omega)] with ω hω _ using hω
            · exact Filter.Eventually.of_forall (fun ω h => absurd h hm)
          rw [← ae_all_iff] at this
          filter_upwards [this] with ω hω m hm using hω m hm
        have h32 := eq_32 M hH2 R P Y hY τ hadm r hr n hn hch
        exact theorem_3_1_unselected M hH2 R P Y hY τ hadm r hr n hn h32
  have hall : ∀ᵐ ω ∂P, ∀ n, Tendsto (fun k => M.V n ((r ω).x (k * τ) n) -
      (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro n
    exact key H n (by omega)
  filter_upwards [hall] with ω hω
  refine ⟨fun n hn => ?_, hω⟩
  exact lemma_3_2 M hH2 R (fun k => Y k ω) (r ω) (hr ω) n hn τ hτ (fun m _ => hω m)
