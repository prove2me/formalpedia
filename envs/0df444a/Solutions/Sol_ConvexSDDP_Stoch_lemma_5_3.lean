-- Prove2me | solution 1 for ConvexSDDP.Stoch.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:47:03.552986+00:00
-- url     : https://prove2.me/submissions/58e81749-d910-4177-b4b0-40677895fdf0

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
open StochasticProg.Multistage

namespace Aux_SDDP53

lemma stage_iter {H : ℕ} (T : Tree H) (n : T.Node) :
    ∀ i, i ≤ (T.stage n).val → (T.stage (T.anc^[i] n)).val = (T.stage n).val - i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    rw [Function.iterate_succ_apply']
    have h2 := T.anc_stage (T.anc^[i] n) (by omega)
    omega

end Aux_SDDP53

open ConvexSDDP.Stoch in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) (τ : ℕ) (hτ : 0 < τ) (hadm : AdmissibleI T ys τ) :
    ∀ k κ n, κ < τ → ¬ IsLeaf T n → ys (k * τ + κ) n = true →
      r.x (k * τ + κ) n = r.x (k * τ) n ∧
      (1 ≤ k → r.Vc (k * τ + κ) n = r.Vc (k * τ) n) := by
  obtain ⟨h0, hleaf, hroot, hchild, hhat, hθβ, hstep⟩ := hr
  intro k κ n hκ hn hsel
  have hfalse := hadm n hn k κ hκ hsel
  -- cut models are frozen along the ancestors of n during the block
  have hVc : ∀ a ∈ asc T n, ∀ j ≤ κ, r.Vc (k * τ + j) a = r.Vc (k * τ) a := by
    intro a ha j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      by_cases hl : IsLeaf T a
      · rw [hleaf _ a hl, hleaf _ a hl]
      · have hys := hfalse a ha j (by omega)
        obtain ⟨-, -, hcut⟩ := (hθβ (k * τ + j) a hl).2 hys
        rw [show k * τ + (j + 1) = (k * τ + j) + 1 by ring, hstep _ a hl]
        funext y
        exact max_eq_left (hcut y)
  have hnmem : n ∈ asc T n := ⟨0, Nat.zero_le _, rfl⟩
  refine ⟨?_, fun _ => hVc n hnmem κ le_rfl⟩
  -- trial points agree along the path, by induction on the stage
  have key : ∀ s, ∀ a, (T.stage a).val = s → a ∈ asc T n → r.x (k * τ + κ) a = r.x (k * τ) a := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro a hs ha
      by_cases har : a = T.root
      · rw [har, hroot, hroot]
      · have hst : (T.stage a).val ≠ 0 := fun h => har (T.root_unique a h)
        have hanc := T.anc_stage a hst
        have hancmem : T.anc a ∈ asc T n := by
          obtain ⟨i, hi, hia⟩ := ha
          have h1 := Aux_SDDP53.stage_iter T n i hi
          rw [hia] at h1
          refine ⟨i + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply', hia]
        have hih := ih (T.stage (T.anc a)).val (by omega) (T.anc a) rfl hancmem
        obtain ⟨hu1, -, -, hx1⟩ := hchild (k * τ + κ) a har
        obtain ⟨hu2, -, -, hx2⟩ := hchild (k * τ) a har
        rw [hx1, hx2, hu1, hu2, hih, hVc a ha κ le_rfl]
  exact key _ n rfl hnmem
