-- Prove2me | solution 1 for BitDFT.tape_extension_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:34:57.260999+00:00
-- url     : https://prove2.me/submissions/50906bdf-1973-4ef5-9846-6f03b2c08761

import Definitions.Def_BitDFT_TapeExtension
namespace BitDFT.TapeExtension
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (M : MultitapeTM) (r : ℕ)
    (cells : Fin (M.k+r) → ℕ → M.Sym) (heads : Fin (M.k+r) → ℕ) (c : M.Cfg) :
    (machine M r).step (embed M r cells heads c) = embed M r cells heads (M.step c) := by
  have hread : (fun j => (embed M r cells heads c).cells (oldTape M r j)
      ((embed M r cells heads c).head (oldTape M r j))) =
      (fun j => c.cells j (c.head j)) := by
    funext j
    simp [embed, oldTape, j.isLt]
  apply cfg_ext
  · change (M.δ c.state _).1 = (M.δ c.state _).1
    rw [hread]
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.step, transition, embed, oldTape, hi]
    · simp [MultitapeTM.step, transition, embed, oldTape, hi]
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.step, transition, embed, oldTape, hi]
    · simp [MultitapeTM.step, transition, embed, oldTape, hi]

theorem run_embed (M : MultitapeTM) (r : ℕ)
    (cells : Fin (M.k+r) → ℕ → M.Sym) (heads : Fin (M.k+r) → ℕ)
    (c : M.Cfg) (t : ℕ) :
    (machine M r).step^[t] (embed M r cells heads c) =
      embed M r cells heads (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_embed, Function.iterate_succ_apply']

theorem init_embed (M : MultitapeTM) (r : ℕ) (x y : List Bool) :
    (machine M r).initCfg x y =
      embed M r (fun _ => M.tapeOf []) (fun _ => 0) (M.initCfg x y) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.initCfg, MultitapeTM.inTape, embed, hi, Fin.ext_iff,
        MultitapeTM.tapeOf, MultitapeTM.bitSym]
      rfl
    · have hz : i.val ≠ 0 := by have := M.two_le_k; omega
      simp [MultitapeTM.initCfg, MultitapeTM.inTape, embed, hi, Fin.ext_iff, hz,
        MultitapeTM.tapeOf]
      rfl
  · funext i; simp [MultitapeTM.initCfg, embed]

theorem halts_iff (M : MultitapeTM) (r : ℕ) (x y w : List Bool) (t : ℕ) :
    (machine M r).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w := by
  have hk : 1 < M.k := by have := M.two_le_k; omega
  unfold MultitapeTM.HaltsWithOutput
  rw [init_embed, run_embed]
  simp [embed, MultitapeTM.outTape, hk]
  intro _
  rfl


end BitDFT.TapeExtension
open BitDFT.TapeExtension IntMul

theorem solution (M : MultitapeTM) (r : ℕ) :
    (∀ cells : Fin (M.k+r) → ℕ → M.Sym, ∀ heads : Fin (M.k+r) → ℕ,
      ∀ c : M.Cfg, ∀ t : ℕ,
      (machine M r).step^[t] (embed M r cells heads c) =
        embed M r cells heads (M.step^[t] c)) ∧
    (∀ x y w : List Bool, ∀ t : ℕ,
      (machine M r).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w) := by
  exact ⟨run_embed M r, halts_iff M r⟩
