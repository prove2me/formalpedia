-- Prove2me | solution 1 for FiniteMagmaE677.no_e677_of_card_four
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-27T21:16:57.433652+00:00
-- url     : https://prove2.me/submissions/da436853-e06d-48bc-8eff-8fa4052d38ac

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-!
# No `E677` magma has four elements

No operation `op : Fin 4 → Fin 4 → Fin 4` satisfies `x = op y (op x (op (op y x) y))` for all
`x y`.

## Proof

`E677Finite4.no_e677_table` replays a RUP refutation of a CNF encoding of the order-4 tables as
ordinary implications between cell equalities `op i j = k`.  Its input clauses are proved from
the hypotheses `Hyp op`: equation 677 (`chain`), the injectivity and surjectivity of every row
(`rowUnique`, `rowTotal`), and the fact that each cell has exactly one value (`cellTotal`,
`cellUnique`).  There is no symmetry breaking.  Each `cNNNN` is one learned clause of the
refutation, and `no_e677_table` derives the empty clause.

`solution` gives `Hyp op` from equation 677: equation 677 at `x i` shows that row `i` reaches
every `x`, and a surjective map `Fin 4 → Fin 4` is injective.

The finite fact is prior work (ETP Zulip: I. Tencer, 2024-12-07; S. Chuks-Onah, 2026-05-01).
The declarations of the namespace `E677Finite4` are copied unchanged from
`lean/E677/FiniteCertificates/OrderFour/` (`Base`, `Block000`, `Block001`) of a private repo
(Adam McKenna); `solution` follows the bridge of `lean/E677/SmallOrderFour.lean` there.
-/

open FiniteMagmaE677

namespace E677Finite4

abbrev Table := Fin 4 → Fin 4 → Fin 4

/-- Semantic hypotheses consumed by the generated RUP proof. -/
structure Hyp (op : Table) : Prop where
  inj : ∀ i, Function.Injective (op i)
  surj : ∀ i, Function.Surjective (op i)
  e677 : ∀ x y, x = op y (op x (op (op y x) y))


theorem cellTotal (x : Fin 4) :
    (x ≠ 0) → (x ≠ 1) → (x ≠ 2) → (x ≠ 3) → False := by
  intro h0 h1 h2 h3
  fin_cases x <;> contradiction

theorem cellUnique (op : Table) (i j k l : Fin 4) (hkl : k ≠ l) :
    op i j = k → op i j = l → False :=
  fun h1 h2 => hkl (h1.symm.trans h2)

theorem rowTotal (op : Table) (hs : ∀ i, Function.Surjective (op i)) (i k : Fin 4) :
    (op i 0 ≠ k) → (op i 1 ≠ k) → (op i 2 ≠ k) → (op i 3 ≠ k) → False := by
  intro h0 h1 h2 h3
  obtain ⟨j, hj⟩ := hs i k
  fin_cases j <;> contradiction

theorem rowUnique (op : Table) (hi : ∀ i, Function.Injective (op i))
    (i j l k : Fin 4) (hjl : j ≠ l) : op i j = k → op i l = k → False :=
  fun h1 h2 => hjl (hi i (h1.trans h2.symm))

theorem chain (op : Table)
    (he : ∀ x y, x = op y (op x (op (op y x) y)))
    (y x a b c : Fin 4) :
    op y x = a → op a y = b → op x b = c → (op y c ≠ x) → False := by
  intro h1 h2 h3 h4
  apply h4
  have ht := (he x y).symm
  rw [h1, h2, h3] at ht
  exact ht

end E677Finite4

namespace E677Finite4

theorem c1252 (op : Table) (h : Hyp op) :
    (op 0 0 = 1) → (op 0 1 ≠ 0) → (op 1 0 = 0) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 0 0 1 0 1) a0 a2 a0 a1

theorem c1254 (op : Table) (h : Hyp op) :
    (op 0 0 = 3) → (op 0 3 ≠ 0) → (op 3 0 = 0) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 0 0 3 0 3) a0 a2 a0 a1

theorem c1255 (op : Table) (h : Hyp op) :
    (op 0 1 = 1) → (op 0 0 ≠ 1) → (op 1 0 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 1 1 ≠ 0 := fun q => (rowUnique op h.inj 1 0 1 0 (by decide)) a2 q
  exact (chain op h.e677 1 0 0 1 1) a2 a0 a0 u0

theorem c1257 (op : Table) (h : Hyp op) :
    (op 0 3 = 3) → (op 0 0 ≠ 3) → (op 3 0 = 0) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 0 3 3 0 0) a0 a2 a2 a1

theorem c1258 (op : Table) (h : Hyp op) :
    (op 1 0 = 0) → (op 0 1 = 1) → (op 1 1 ≠ 0) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 1 0 0 1 1) a0 a1 a1 a2

theorem c1259 (op : Table) (h : Hyp op) :
    (op 1 1 = 0) → (op 0 1 = 1) → (op 1 0 ≠ 1) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 1 1 0 1 0) a0 a1 a0 a2

theorem c1263 (op : Table) (h : Hyp op) :
    (op 1 1 = 2) → (op 1 2 ≠ 1) → (op 2 1 = 1) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 1 1 2 1 2) a0 a2 a0 a1

theorem c1264 (op : Table) (h : Hyp op) :
    (op 1 1 = 3) → (op 1 3 ≠ 1) → (op 3 1 = 1) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 1 1 3 1 3) a0 a2 a0 a1

theorem c1265 (op : Table) (h : Hyp op) :
    (op 1 2 = 2) → (op 1 1 ≠ 2) → (op 2 1 = 1) → False := by
  intro a0 a1 a2
  have u0 : op 2 2 ≠ 1 := fun q => (rowUnique op h.inj 2 1 2 1 (by decide)) a2 q
  exact (chain op h.e677 2 1 1 2 2) a2 a0 a0 u0

theorem c1266 (op : Table) (h : Hyp op) :
    (op 1 3 = 3) → (op 1 1 ≠ 3) → (op 3 1 = 1) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 1 3 3 1 1) a0 a2 a2 a1

theorem c1267 (op : Table) (h : Hyp op) :
    (op 2 0 = 0) → (op 0 2 = 2) → (op 2 2 ≠ 0) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 2 0 0 2 2) a0 a1 a1 a2

theorem c1269 (op : Table) (h : Hyp op) :
    (op 2 2 = 0) → (op 0 2 = 2) → (op 2 0 ≠ 2) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 2 2 0 2 0) a0 a1 a0 a2

theorem c1270 (op : Table) (h : Hyp op) :
    (op 2 2 = 1) → (op 1 2 = 2) → (op 2 1 ≠ 2) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 2 2 1 2 1) a0 a1 a0 a2

theorem c1274 (op : Table) (h : Hyp op) :
    (op 2 2 = 3) → (op 2 3 ≠ 2) → (op 3 2 = 2) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 2 2 3 2 3) a0 a2 a0 a1

theorem c1275 (op : Table) (h : Hyp op) :
    (op 2 3 = 3) → (op 2 2 ≠ 3) → (op 3 2 = 2) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 2 3 3 2 2) a0 a2 a2 a1

theorem c1277 (op : Table) (h : Hyp op) :
    (op 3 1 = 1) → (op 1 3 = 3) → (op 3 3 ≠ 1) → False := by
  intro a0 a1 a2
  have u0 : op 1 1 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) q a1
  exact (c1266 op h) a1 u0 a0

theorem c1278 (op : Table) (h : Hyp op) :
    (op 3 2 = 2) → (op 2 3 = 3) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q a1
  exact (c1275 op h) a1 u0 a0

theorem c1279 (op : Table) (h : Hyp op) :
    (op 3 3 = 0) → (op 0 3 = 3) → (op 3 0 ≠ 3) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 3 3 0 3 0) a0 a1 a0 a2

theorem c1280 (op : Table) (h : Hyp op) :
    (op 3 3 = 1) → (op 1 3 = 3) → (op 3 1 ≠ 3) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 3 3 1 3 1) a0 a1 a0 a2

theorem c1281 (op : Table) (h : Hyp op) :
    (op 3 3 = 2) → (op 2 3 = 3) → (op 3 2 ≠ 3) → False := by
  intro a0 a1 a2
  exact (chain op h.e677 3 3 2 3 2) a0 a1 a0 a2

theorem c1285 (op : Table) (h : Hyp op) :
    (op 2 3 = 2) → (op 3 2 = 2) → (op 3 3 = 3) → False := by
  intro a0 a1 a2
  have u0 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) q a0
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a2
  have u2 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 2 2 (by decide)) q a1
  have u3 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) q a1
  have u4 : op 2 3 ≠ 3 := fun q => (c1278 op h) a1 q u1
  have u5 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 3 2 3 3) a0 q a2 u4
  have u6 : op 2 2 ≠ 0 := fun q => (chain op h.e677 3 2 2 2 0) a1 a0 q u2
  have u7 : op 2 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u6 q u0 u5)
  exact (chain op h.e677 3 2 2 2 1) a1 a0 u7 u3

theorem c1286 (op : Table) (h : Hyp op) :
    (op 2 2 = 0) → (op 2 2 ≠ 2) → (op 2 3 ≠ 2) → (op 3 2 = 2) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) q a0
  have u1 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) a0 q
  have u2 : op 2 3 ≠ 3 := fun q => (c1278 op h) a3 q a4
  have u3 : op 2 2 ≠ 3 := fun q => (c1274 op h) q a2 a3
  have u4 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u1 q a2 u2)
  have u5 : op 2 1 ≠ 1 := fun q => (rowUnique op h.inj 2 1 3 1 (by decide)) q u4
  have u6 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 2 1 3) a3 u4 q a4
  have u7 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q u6 u3 u2)
  have u8 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u0 u5 q u6)
  have u9 : op 2 0 ≠ 2 := fun q => (cellUnique op 2 0 2 3 (by decide)) q u7
  have u10 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 2 0 1 2) a0 q u8 a1
  have u11 : op 0 2 ≠ 2 := fun q => (c1269 op h) a0 q u9
  have u12 : op 0 2 ≠ 0 := fun q => (chain op h.e677 2 2 0 0 3) a0 q u7 a2
  have u13 : op 0 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u12 u10 u11 q)
  exact (chain op h.e677 2 0 3 2 3) u7 a3 u13 u1

theorem c1287 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 2) → (op 2 3 ≠ 2) → (op 3 2 = 2) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 3 ≠ 3 := fun q => (c1278 op h) a2 q a3
  have u1 : op 2 2 ≠ 3 := fun q => (c1274 op h) q a1 a2
  have u2 : op 2 2 ≠ 0 := fun q => (c1286 op h) q a0 a1 a2 a3
  have u3 : op 2 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u2 q a0 u1)
  have u4 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 2 1 (by decide)) q u3
  have u5 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) u3 q
  have u6 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u5 a1 u0)
  have u7 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) q u6
  have u8 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 2 0 3) a2 u6 q a3
  have u9 : op 2 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) u8 q u1 u0)
  have u10 : op 2 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u7 u4 q u8)
  have u11 : op 2 1 ≠ 2 := fun q => (cellUnique op 2 1 2 3 (by decide)) q u9
  have u12 : op 1 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 3) u3 q u9 a1
  have u13 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 2 1 0 2) u3 q u10 a0
  have u14 : op 1 2 ≠ 2 := fun q => (c1270 op h) u3 q u11
  have u15 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u13 u12 u14 q)
  exact (chain op h.e677 2 1 3 2 3) u9 a2 u15 u5

theorem c1288 (op : Table) (h : Hyp op) :
    (op 2 3 = 0) → (op 2 0 ≠ 2) → (op 3 2 = 2) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) q a0
  have u1 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) q a2
  have u2 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 2 0 3) a2 a0 q a3
  have u3 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u0 q a1 u2)
  exact (chain op h.e677 3 2 2 0 1) a2 a0 u3 u1

theorem c1289 (op : Table) (h : Hyp op) :
    (op 3 2 = 2) → (op 3 3 = 3) → False := by
  intro a0 a1
  have u0 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 2 2 (by decide)) q a0
  have u1 : op 3 3 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) a0 q
  have u2 : op 2 3 ≠ 3 := fun q => (c1278 op h) a0 q u1
  have u3 : op 2 3 ≠ 2 := fun q => (c1285 op h) q a0 a1
  have u4 : op 2 2 = 2 := Classical.byContradiction (fun q => (c1287 op h) q u3 a0 u1)
  have u5 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 2 2 (by decide)) q u4
  have u6 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q u4
  have u7 : op 2 3 ≠ 0 := fun q => (c1288 op h) q u5 a0 u1
  have u8 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u7 q u3 u2)
  have u9 : op 2 1 ≠ 1 := fun q => (rowUnique op h.inj 2 1 3 1 (by decide)) q u8
  have u10 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 2 1 3) a0 u8 q u1
  have u11 : op 2 1 ≠ 0 := fun q => (chain op h.e677 3 2 2 1 0) a0 u8 q u0
  exact (cellTotal (op 2 1)) u11 u9 u6 u10

theorem c1291 (op : Table) (h : Hyp op) :
    (op 1 2 = 2) → (op 2 0 = 3) → (op 2 1 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) a0 q
  exact (chain op h.e677 1 2 2 0 3) a0 a2 a1 u0

theorem c1292 (op : Table) (h : Hyp op) :
    (op 1 2 = 0) → (op 2 1 ≠ 3) → (op 2 2 ≠ 3) → (op 2 3 = 1) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 1 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) q a0
  have u1 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 2 3 0 (by decide)) a0 q
  have u2 : op 3 0 ≠ 2 := fun q => (chain op h.e677 2 3 1 0 2) a3 a0 q a2
  have u3 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a4
  have u4 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u5 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u6 : op 3 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) u2 q u5 u4)
  have u7 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u6
  have u8 : op 1 1 ≠ 3 := fun q => (chain op h.e677 3 1 2 1 3) u6 a3 q u3
  have u9 : op 1 1 ≠ 1 := fun q => (chain op h.e677 3 1 2 1 1) u6 a3 q u7
  have u10 : op 1 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) u0 u9 q u8)
  have u11 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u10 q
  have u12 : op 3 2 = 1 := Classical.byContradiction (fun q => (chain op h.e677 3 1 2 1 2) u6 a3
    u10 q)
  have u13 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) q u10 u12 u8
  have u14 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 2 1) q u6 u12 u8
  exact (cellTotal (op 1 3)) u1 u13 u11 u14

theorem c1293 (op : Table) (h : Hyp op) :
    (op 2 1 ≠ 3) → (op 2 2 = 2) → (op 2 3 = 1) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 2 ≠ 3 := fun q => (cellUnique op 2 2 2 3 (by decide)) a1 q
  have u1 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q a1
  have u2 : op 1 2 ≠ 3 := fun q => (chain op h.e677 2 3 1 3 3) a2 q a4 a3
  have u3 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u4 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u5 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a0 u0 a3)
  have u6 : op 1 2 ≠ 0 := fun q => (c1292 op h) q a0 u0 a2 a4
  have u7 : op 2 1 ≠ 1 := fun q => (rowUnique op h.inj 2 1 3 1 (by decide)) q a2
  have u8 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u7 u1 a0)
  have u9 : op 1 2 ≠ 2 := fun q => (c1291 op h) q u5 u8
  have u10 : op 1 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u6 q u9 u2)
  have u11 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 1 2 1 (by decide)) q u10
  have u12 : op 1 1 ≠ 2 := fun q => (chain op h.e677 1 2 1 2 2) u10 q a1 u9
  have u13 : op 3 1 ≠ 2 := fun q => (chain op h.e677 2 3 1 1 2) a2 u10 q u0
  have u14 : op 1 1 ≠ 3 := fun q => (chain op h.e677 1 2 1 3 1) u10 q a2 u12
  have u15 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u13 u4
    u3)
  have u16 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q u11 u12 u14)
  have u17 : op 1 3 ≠ 2 := fun q => (chain op h.e677 1 3 2 0 2) q u8 u15 u2
  exact (chain op h.e677 1 2 1 0 3) u10 u16 u5 u17

theorem c1294 (op : Table) (h : Hyp op) :
    (op 1 2 = 1) → (op 1 2 ≠ 2) → (op 2 2 = 2) → (op 2 3 = 1) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 1 3 (by decide)) a0 q
  have u1 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) q a0
  have u2 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 1 2 1 (by decide)) q a0
  have u3 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 2 3 1 (by decide)) a0 q
  have u4 : op 1 1 ≠ 2 := fun q => (chain op h.e677 1 2 1 2 2) a0 q a2 a1
  have u5 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u6 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u7 : op 2 2 ≠ 3 := fun q => (cellUnique op 2 2 2 3 (by decide)) a2 q
  have u8 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q a2
  have u9 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 3 1 (by decide)) q a3
  have u10 : op 1 1 ≠ 3 := fun q => (chain op h.e677 1 2 1 3 1) a0 q a3 u4
  have u11 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q u2 u4 u10)
  have u12 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 1 3 0 (by decide)) u11 q
  have u13 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 1 1 1 0) q a0 u11 u9
  have u14 : op 0 1 ≠ 1 := fun q => (c1259 op h) u11 q u1
  have u15 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 1 0 2 1) u11 q a0 u2
  have u16 : op 3 1 ≠ 2 := fun q => (chain op h.e677 2 3 1 1 2) a3 a0 q u7
  have u17 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u16 u6
    u5)
  have u18 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 2 (by decide)) q u17
  have u19 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 2 1 0) u17 a3 q u18
  have u20 : op 0 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u19 u14 u15 q)
  have u21 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 3) u11 u20 q u3
  have u22 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u12 u3 q u21)
  have u23 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 3 2 3 3) u22 q a4 u21
  have u24 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 3 2 0 2) u22 q u17 u0
  exact (cellTotal (op 2 1)) u24 u13 u8 u23

theorem c1295 (op : Table) (h : Hyp op) :
    (op 1 2 = 0) → (op 2 0 ≠ 3) → (op 2 2 ≠ 3) → (op 2 3 = 1) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 1 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) q a0
  have u1 : op 3 0 ≠ 2 := fun q => (chain op h.e677 2 3 1 0 2) a3 a0 q a2
  have u2 : op 3 0 ≠ 0 := fun q => (chain op h.e677 2 3 1 0 0) a3 a0 q a1
  have u3 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a4
  have u4 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u5 : op 3 0 ≠ 3 := fun q => (rowUnique op h.inj 3 0 3 3 (by decide)) q a4
  have u6 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u7 : op 3 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) u1 q u6 u4)
  have u8 : op 3 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u2 q u1 u5)
  have u9 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u7
  have u10 : op 1 1 ≠ 3 := fun q => (chain op h.e677 3 1 2 1 3) u7 a3 q u3
  have u11 : op 1 1 ≠ 1 := fun q => (chain op h.e677 3 1 2 1 1) u7 a3 q u9
  have u12 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) u8 q
  have u13 : op 1 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) u0 u11 q u10)
  exact (chain op h.e677 3 1 2 1 2) u7 a3 u13 u12

theorem c1296 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 2) → (op 1 2 ≠ 0) → (op 1 2 ≠ 3) → (op 2 2 = 2) → (op 2 3 = 1) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) a1 q a0 a2)
  exact (c1294 op h) u0 a0 a3 a4 a5

theorem c1297 (op : Table) (h : Hyp op) :
    (op 2 3 = 1) → (op 2 2 = 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 2 ≠ 3 := fun q => (cellUnique op 2 2 2 3 (by decide)) a1 q
  have u1 : op 1 2 ≠ 3 := fun q => (chain op h.e677 2 3 1 3 3) a0 q a3 a2
  have u2 : op 2 1 = 3 := Classical.byContradiction (fun q => (c1293 op h) q a1 a0 a2 a3)
  have u3 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 1 3 (by decide)) q u2
  have u4 : op 1 2 ≠ 0 := fun q => (c1295 op h) q u3 u0 a0 a3
  have u5 : op 1 2 = 2 := Classical.byContradiction (fun q => (c1296 op h) q u4 u1 a1 a0 a3)
  have u6 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q u5
  exact (chain op h.e677 1 2 2 3 1) u5 u2 a0 u6

theorem c1298 (op : Table) (h : Hyp op) :
    (op 1 2 = 2) → (op 2 1 ≠ 2) → (op 2 3 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) q a0
  have u1 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q a0
  have u2 : op 2 1 ≠ 1 := fun q => (c1265 op h) a0 u1 q
  have u3 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 2 2 3 0) a0 q a2 u0
  have u4 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q a2
  exact (cellTotal (op 2 1)) u4 u2 a1 u3

theorem c1299 (op : Table) (h : Hyp op) :
    (op 1 3 = 2) → (op 2 0 = 3) → (op 2 1 = 1) → (op 2 2 = 2) → (op 2 3 = 0) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q a0
  have u1 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a5
  have u2 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a5
  have u3 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a5
  have u4 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a5
  have u5 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) q a4
  have u6 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q a4
  have u7 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) q a4
  have u8 : op 3 2 ≠ 1 := fun q => (chain op h.e677 3 2 1 2 2) q a0 a3 u4
  have u9 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u8 u4 u3)
  have u10 : op 0 0 ≠ 1 := fun q => (chain op h.e677 2 0 3 0 1) a1 u9 q u6
  have u11 : op 0 0 ≠ 0 := fun q => (chain op h.e677 2 0 3 0 0) a1 u9 q u5
  have u12 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 2 0 2 2) u9 q a3 u4
  have u13 : op 0 3 ≠ 0 := fun q => (chain op h.e677 3 2 0 0 3) u9 q a1 u2
  have u14 : op 0 0 ≠ 2 := fun q => (chain op h.e677 2 0 3 0 2) a1 u9 q u7
  have u15 : op 0 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u11 u10 u14 q)
  have u16 : op 0 1 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) u15 q
  have u17 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 0 3 3 (by decide)) u15 q
  have u18 : op 0 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u13 q u12 u17)
  have u19 : op 3 1 = 2 := Classical.byContradiction (fun q => (chain op h.e677 3 2 0 1 1) u9 u18
    a2 q)
  have u20 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u19
  have u21 : op 1 0 ≠ 1 := fun q => (chain op h.e677 3 1 2 0 1) u19 a4 q u20
  have u22 : op 1 0 ≠ 3 := fun q => (chain op h.e677 3 1 2 0 3) u19 a4 q u1
  have u23 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u20 u8
    u1)
  have u24 : op 1 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) q u21 u0 u22)
  exact (chain op h.e677 0 3 1 0 1) u18 u24 u23 u16

theorem c1300 (op : Table) (h : Hyp op) :
    (op 1 2 = 1) → (op 1 1 ≠ 2) → (op 2 0 ≠ 1) → (op 2 1 = 1) → (op 2 3 ≠ 1) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 1 ≠ 3 := fun q => (chain op h.e677 2 1 1 1 3) a3 a0 q a4
  have u1 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 1 2 1 (by decide)) q a0
  have u2 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q u1 a1 u0)
  exact (chain op h.e677 2 1 1 1 0) a3 a0 u2 a2

theorem c1301 (op : Table) (h : Hyp op) :
    (op 2 1 ≠ 3) → (op 1 1 ≠ 2) → (op 2 2 = 2) → (op 2 3 = 0) → (op 2 3 ≠ 3) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a5
  have u1 : op 2 2 ≠ 1 := fun q => (cellUnique op 2 2 1 2 (by decide)) q a2
  have u2 : op 2 2 ≠ 3 := fun q => (cellUnique op 2 2 2 3 (by decide)) a2 q
  have u3 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q a2
  have u4 : op 2 3 ≠ 1 := fun q => (c1297 op h) q a2 a4 a5
  have u5 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q a3
  have u6 : op 1 2 ≠ 2 := fun q => (c1298 op h) q u3 a3
  have u7 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a0 u2 a4)
  have u8 : op 2 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u5 q u3 a0)
  have u9 : op 2 0 ≠ 1 := fun q => (cellUnique op 2 0 1 3 (by decide)) q u7
  have u10 : op 1 3 ≠ 2 := fun q => (c1299 op h) q u7 u8 a2 a3 a5
  have u11 : op 1 2 ≠ 1 := fun q => (c1300 op h) q a1 u9 u8 u4
  have u12 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q a1 u6
    u10)
  have u13 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 1 1 0 2) u8 q u12 u1
  have u14 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u13 u11 u6 q)
  have u15 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 2 3 1 1) u14 q u8 a1
  have u16 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 2 3 2 2) u14 q a2 u6
  have u17 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 2 3 0 3) u14 q u7 u10
  exact (cellTotal (op 3 1)) u17 u15 u16 u0

theorem c1304 (op : Table) (h : Hyp op) :
    (op 1 3 = 2) → (op 2 1 = 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2
  have u0 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 2 3 (by decide)) a0 q
  exact (chain op h.e677 1 3 2 3 3) a0 a1 a2 u0

theorem c1305 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 2) → (op 2 2 = 2) → (op 2 3 = 0) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u1 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a4
  have u2 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u3 : op 2 2 ≠ 1 := fun q => (cellUnique op 2 2 1 2 (by decide)) q a1
  have u4 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q a1
  have u5 : op 2 3 ≠ 1 := fun q => (c1297 op h) q a1 a3 a4
  have u6 : op 1 2 ≠ 2 := fun q => (c1298 op h) q u4 a2
  have u7 : op 2 1 = 3 := Classical.byContradiction (fun q => (c1301 op h) q a0 a1 a2 a3 a4)
  have u8 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 3 (by decide)) q u7
  have u9 : op 1 3 ≠ 2 := fun q => (c1304 op h) q u7 a4
  have u10 : op 2 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 1) q u8 u3
    u5)
  have u11 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q a0 u6
    u9)
  have u12 : op 1 0 ≠ 1 := fun q => (cellUnique op 1 0 1 2 (by decide)) q u11
  have u13 : op 3 2 ≠ 0 := fun q => (chain op h.e677 2 1 3 0 2) u7 q u11 u3
  have u14 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u13 q u2 u1)
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 3 2 1 1 3) u14 q u7 u0
  have u16 : op 1 1 ≠ 3 := fun q => (chain op h.e677 2 1 3 1 3) u7 u14 q u5
  have u17 : op 1 1 ≠ 1 := fun q => (chain op h.e677 2 1 3 1 1) u7 u14 q u8
  have u18 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q u17 a0 u16)
  have u19 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u12 u17 q
    u15)
  exact (chain op h.e677 1 2 1 0 1) u19 u18 u10 a0

theorem c1306 (op : Table) (h : Hyp op) :
    (op 2 2 = 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 2 ≠ 1 := fun q => (cellUnique op 2 2 1 2 (by decide)) q a0
  have u1 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q a0
  have u2 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a3
  have u3 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a3
  have u4 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a3
  have u5 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a3
  have u6 : op 2 3 ≠ 1 := fun q => (c1297 op h) q a0 a2 a3
  have u7 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u6 a1 a2)
  have u8 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q u7
  have u9 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1305 op h) q a0 u7 a2 a3)
  have u10 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q u9
  have u11 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u9
  have u12 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u9 q
  have u13 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) u9 q
  have u14 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u9 q
  have u15 : op 1 2 ≠ 1 := fun q => (chain op h.e677 1 2 1 2 2) q u9 a0 u13
  have u16 : op 2 1 ≠ 1 := fun q => (c1263 op h) u9 u15 q
  have u17 : op 2 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 1) q u16 u0
    u6)
  have u18 : op 2 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u8 u16 u1 q)
  have u19 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 1 2 3 1) u9 u18 q u11
  have u20 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u11 u15
    u19)
  have u21 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 1 2 3 3) u9 u18 q u19
  have u22 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 1 3 (by decide)) u20 q
  have u23 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 1 2 1) u20 u9 q u10
  have u24 : op 3 2 ≠ 0 := fun q => (chain op h.e677 2 1 3 0 1) u18 q u20 u16
  have u25 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u22 u12 q
    u21)
  have u26 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 1 2) q u20 u9 u23
  have u27 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u24 q u5 u4)
  have u28 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 2 3 1 3) u25 q u18 u14
  have u29 : op 0 3 ≠ 1 := fun q => (chain op h.e677 2 0 1 3 1) u17 u25 q u8
  have u30 : op 3 1 ≠ 2 := fun q => (chain op h.e677 3 1 2 0 1) q u7 u20 u28
  have u31 : op 0 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) q u26 u23
    u29)
  have u32 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u30 u5
    u2)
  have u33 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u28 u30 u3)
  have u34 : op 0 0 ≠ 3 := fun q => (cellUnique op 0 0 1 3 (by decide)) u31 q
  have u35 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 3 0 1 0) q u31 u33 u34
  have u36 : op 0 3 ≠ 2 := fun q => (chain op h.e677 0 3 2 1 0) q u17 u33 u34
  have u37 : op 0 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u35 u29 u36 q)
  have u38 : op 0 1 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) q u37
  exact (chain op h.e677 0 3 3 2 1) u37 u32 u27 u38

theorem c1307 (op : Table) (h : Hyp op) :
    (op 2 1 = 3) → (op 1 1 = 2) → (op 2 2 ≠ 2) → (op 2 3 ≠ 2) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 1 ≠ 2 := fun q => (cellUnique op 2 1 2 3 (by decide)) q a0
  have u1 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 1 2 3 (by decide)) a0 q
  have u2 : op 1 3 ≠ 2 := fun q => (c1304 op h) q a0 a4
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q a1
  have u4 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 1 2 (by decide)) q a1
  have u5 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a4
  have u6 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u7 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q u0 a2 a3)
  have u8 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 1 2 3 1) a1 a0 q u3
  have u9 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 3 (by decide)) q a0
  have u10 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 1 2 3 3) a1 a0 q u8
  have u11 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u8 u2 u10)
  have u12 : op 3 2 ≠ 1 := fun q => (chain op h.e677 3 2 1 0 2) q u11 u7 u6
  have u13 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u12 u6 u5)
  have u14 : op 1 0 ≠ 1 := fun q => (chain op h.e677 2 1 3 0 1) a0 u13 q u9
  have u15 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u14 u3 q
    u8)
  have u16 : op 2 2 ≠ 0 := fun q => (chain op h.e677 1 2 1 2 0) u15 a1 q u4
  have u17 : op 2 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 3) q u15 a0 a3
  exact (cellTotal (op 2 2)) u16 u17 a2 u1

theorem c1308 (op : Table) (h : Hyp op) :
    (op 1 0 = 1) → (op 1 1 = 2) → (op 2 1 ≠ 1) → (op 2 1 ≠ 3) → (op 3 1 ≠ 3) → (op 3 2 = 0) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 1 3 (by decide)) a0 q
  have u1 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) a0 q
  have u2 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) a0 q
  have u3 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 1) a1 q a0 u1
  have u4 : op 3 2 ≠ 1 := fun q => (cellUnique op 3 2 0 1 (by decide)) a5 q
  have u5 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a5
  have u6 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q a1
  have u7 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) a1 q
  have u8 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u3 a2 q a3)
  have u9 : op 2 3 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) u8 q
  have u10 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 1 2 1) a0 a1 q u6
  have u11 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 1 2) q a0 a1 u10
  have u12 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 0 2 (by decide)) a5 q
  have u13 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 2 0 1 2) a5 q u8 u12
  have u14 : op 0 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) q u11 u10
    u13)
  have u15 : op 2 0 ≠ 3 := fun q => (chain op h.e677 2 0 3 0 1) q a5 u14 u3
  have u16 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 1 2 (by decide)) q u8
  have u17 : op 1 2 ≠ 3 := fun q => (chain op h.e677 1 1 2 2 3) a1 u8 q u2
  have u18 : op 1 3 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u0 u7 u17
    q)
  have u19 : op 3 1 ≠ 1 := fun q => (c1266 op h) u18 u7 q
  have u20 : op 3 3 ≠ 1 := fun q => (c1280 op h) q u18 a4
  have u21 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u19 u4
    u20)
  have u22 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u5 u19 q a4)
  have u23 : op 2 3 ≠ 3 := fun q => (chain op h.e677 2 3 3 0 1) q a5 u21 a3
  have u24 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 1 2 0 1) u22 q a0 u19
  have u25 : op 2 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) u15 a3 q
    u23)
  have u26 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u24 q u9 u23)
  have u27 : op 2 0 ≠ 0 := fun q => (chain op h.e677 2 2 3 0 0) u25 a5 q u16
  have u28 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 3 1 (by decide)) q u26
  exact (cellTotal (op 2 0)) u27 u28 u16 u15

theorem c1309 (op : Table) (h : Hyp op) :
    (op 1 2 = 1) → (op 1 1 = 2) → (op 2 1 ≠ 3) → (op 2 2 ≠ 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 1 2 (by decide)) q a1
  have u1 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) a1 q
  have u2 : op 2 2 ≠ 0 := fun q => (chain op h.e677 1 2 1 2 0) a0 a1 q u0
  have u3 : op 2 2 ≠ 3 := fun q => (chain op h.e677 1 2 1 2 3) a0 a1 q u1
  have u4 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a2 u3 a5)
  have u5 : op 2 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u2 q a3 u3)
  have u6 : op 2 0 ≠ 2 := fun q => (cellUnique op 2 0 2 3 (by decide)) q u4
  have u7 : op 2 1 ≠ 2 := fun q => (chain op h.e677 2 2 1 1 2) u5 a0 q a3
  exact (rowTotal op h.surj 2 2) u6 u7 a3 a4

theorem c1310 (op : Table) (h : Hyp op) :
    (op 1 3 = 1) → (op 1 1 = 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 2 ≠ 1) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 3 ≠ 0 := fun q => (cellUnique op 1 3 0 1 (by decide)) q a0
  have u1 : op 1 3 ≠ 2 := fun q => (cellUnique op 1 3 1 2 (by decide)) a0 q
  have u2 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 1 3 (by decide)) a0 q
  have u3 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) q a0
  have u4 : op 3 2 ≠ 3 := fun q => (chain op h.e677 1 3 1 2 3) a0 a1 q u2
  have u5 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 1 2 3 1) a1 q a0 u3
  have u6 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a5
  have u7 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a5
  have u8 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a5
  have u9 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q a1
  have u10 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q a4 u8 u4)
  have u11 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 2 0 (by decide)) q u10
  have u12 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q u10
  have u13 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 1 1 1 2) q a0 a1 a4
  have u14 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u13 a4
    u6)
  have u15 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u12 u13 q u7)
  have u16 : op 1 0 = 3 := Classical.byContradiction (fun q => (chain op h.e677 1 3 1 2 0) a0 a1
    u10 q)
  have u17 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 3 (by decide)) q u16
  have u18 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 3 2 1) u16 u15 q u9
  have u19 : op 1 2 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u17 u9 q
    u0)
  have u20 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 1 1 0) u14 a0 q u11
  have u21 : op 0 1 ≠ 3 := fun q => (chain op h.e677 0 1 3 1 2) q u14 a1 u18
  have u22 : op 0 1 ≠ 1 := fun q => (chain op h.e677 3 0 1 1 1) u14 a0 q u12
  have u23 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u20 u22 q u21)
  have u24 : op 2 2 ≠ 3 := fun q => (chain op h.e677 1 2 0 2 3) u19 u23 q u1
  have u25 : op 2 0 ≠ 3 := fun q => (chain op h.e677 0 1 2 3 1) u23 q a0 u22
  exact (rowTotal op h.surj 2 3) u25 u5 u24 a3

theorem c1311 (op : Table) (h : Hyp op) :
    (op 3 2 ≠ 1) → (op 1 1 = 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a4
  have u1 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a4
  have u2 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u3 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a2 a3 a4
  have u4 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q a1
  have u5 : op 2 1 ≠ 3 := fun q => (c1307 op h) q a1 u3 a2 a4
  have u6 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q a0 u2 u1)
  have u7 : op 1 2 ≠ 1 := fun q => (c1309 op h) q a1 u5 u3 a2 a3
  have u8 : op 2 1 ≠ 1 := fun q => (c1263 op h) a1 u7 q
  have u9 : op 1 3 ≠ 1 := fun q => (c1310 op h) q a1 a2 a3 a0 a4
  have u10 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u4 u7
    u9)
  exact (c1308 op h) u10 a1 u8 u5 u0 u6

theorem c1312 (op : Table) (h : Hyp op) :
    (op 1 1 = 2) → (op 1 2 ≠ 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q a0
  have u1 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) a0 q
  have u2 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) a0 q
  have u3 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a2 a3 a4
  have u5 : op 2 1 ≠ 3 := fun q => (c1307 op h) q a0 u4 a2 a4
  have u6 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1311 op h) q a0 a2 a3 a4)
  have u7 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) q a0 u6 u1
  have u8 : op 1 2 ≠ 1 := fun q => (c1309 op h) q a0 u5 u4 a2 a3
  have u9 : op 2 1 ≠ 1 := fun q => (c1263 op h) a0 u8 q
  have u10 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u0 u8
    u7)
  have u11 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 1) a0 q u10 u0
  have u12 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u11 u9 q u5)
  have u13 : op 2 2 ≠ 0 := fun q => (chain op h.e677 2 1 2 0 1) u12 q u10 u9
  have u14 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 2 3 1 2) q u6 u12 u4
  have u15 : op 2 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u13 q u4 u14)
  have u16 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q u5 u14
    a3)
  have u17 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 2 1 0 3) u15 q u16 a2
  have u18 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u17 u8 a1 q)
  have u19 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 2 3 3 (by decide)) u18 q
  have u20 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u7 u2 u19)
  exact (chain op h.e677 3 2 1 0 3) u6 u20 u16 u3

theorem c1313 (op : Table) (h : Hyp op) :
    (op 3 2 = 1) → (op 1 0 = 1) → (op 1 3 = 2) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op
      3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q a2
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a6
  have u2 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a4 a5 a6
  have u3 : op 1 2 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) a1 q
  have u4 : op 2 2 ≠ 3 := fun q => (chain op h.e677 3 2 1 2 3) a0 a2 q u1
  have u5 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a3 u4 a5)
  have u6 : op 2 0 ≠ 2 := fun q => (cellUnique op 2 0 2 3 (by decide)) q u5
  have u7 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u6 q u2 a4)
  have u8 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q u7
  have u9 : op 1 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 1 3 2 2 1) a2 u7 a0
    q)
  have u10 : op 2 2 ≠ 0 := fun q => (chain op h.e677 2 1 2 0 1) u7 q a1 u8
  have u11 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) u9 q
  have u12 : op 2 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u10 q u2 u4)
  have u13 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u3 u0 u11)
  exact (chain op h.e677 2 2 1 0 3) u12 u13 u5 a4

theorem c1314 (op : Table) (h : Hyp op) :
    (op 1 0 = 1) → (op 1 2 ≠ 2) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 1 0 ≠ 2 := fun q => (cellUnique op 1 0 1 2 (by decide)) a0 q
  have u1 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 1 3 (by decide)) a0 q
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a5
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a5
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a3 a4 a5
  have u5 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a1 a3 a4 a5
  have u6 : op 1 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u0 u5 a1 q)
  have u7 : op 3 2 ≠ 1 := fun q => (c1313 op h) q a0 u6 a2 a3 a4 a5
  have u8 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u7 u3 u2)
  have u9 : op 2 1 ≠ 2 := fun q => (chain op h.e677 1 3 2 2 0) u6 q u8 u1
  have u10 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q u9 u4
    a3)
  have u11 : op 2 0 ≠ 3 := fun q => (cellUnique op 2 0 2 3 (by decide)) u10 q
  have u12 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 2 3 0 2) q u8 u10 u4
  exact (rowTotal op h.surj 2 3) u11 a2 u12 a4

theorem c1315 (op : Table) (h : Hyp op) :
    (op 2 0 = 2) → (op 2 1 ≠ 3) → (op 2 2 ≠ 2) → (op 2 3 ≠ 3) → (op 3 2 = 0) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 0 ≠ 3 := fun q => (cellUnique op 2 0 2 3 (by decide)) a0 q
  have u1 : op 2 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) u0 a1 q a3)
  exact (chain op h.e677 2 2 3 0 2) u1 a4 a0 a2

theorem c1316 (op : Table) (h : Hyp op) :
    (op 1 3 = 2) → (op 0 0 ≠ 1) → (op 0 3 ≠ 1) → (op 1 0 ≠ 1) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op
      2 1 = 2) → (op 2 2 ≠ 2) → (op 2 2 ≠ 3) → (op 3 2 = 0) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : op 1 3 ≠ 1 := fun q => (cellUnique op 1 3 1 2 (by decide)) q a0
  have u1 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q a0
  have u2 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) a3 a4 q u0)
  have u3 : op 2 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 2) q u2 a6 a7
  have u4 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u3 a7 a8)
  have u5 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 2 0 1 2) u4 q a6 a7
  have u6 : op 0 1 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) a1 q u5 a2)
  have u7 : op 1 0 ≠ 3 := fun q => (chain op h.e677 0 1 1 3 2) u6 q a0 u5
  have u8 : op 1 0 ≠ 0 := fun q => (c1255 op h) u6 a1 q
  exact (cellTotal (op 1 0)) u8 a3 u1 u7

theorem c1317 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 3) → (op 0 3 ≠ 1) → (op 1 0 ≠ 1) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 1 2 ≠ 2) → (op
      2 1 = 2) → (op 2 1 ≠ 3) → (op 2 2 ≠ 2) → (op 2 3 ≠ 3) → (op 3 2 = 0) → (op 3 3 ≠ 2) → False
      := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have u0 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a7 a0 a9)
  have u1 : op 2 1 ≠ 0 := fun q => (cellUnique op 2 1 0 2 (by decide)) q a6
  have u2 : op 0 0 ≠ 1 := fun q => (chain op h.e677 2 0 3 0 1) u0 a10 q u1
  have u3 : op 2 0 ≠ 0 := fun q => (cellUnique op 2 0 0 3 (by decide)) q u0
  have u4 : op 0 0 ≠ 0 := fun q => (chain op h.e677 2 0 3 0 0) u0 a10 q u3
  have u5 : op 0 3 ≠ 0 := fun q => (chain op h.e677 3 2 0 0 3) a10 q u0 a11
  have u6 : op 1 3 ≠ 2 := fun q => (c1316 op h) q u2 a1 a2 a3 a4 a6 a8 a0 a10
  have u7 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q a4 a5 u6)
  have u8 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 2 (by decide)) q u7
  have u9 : op 0 2 ≠ 0 := fun q => (chain op h.e677 1 0 2 2 0) u7 a6 q u8
  have u10 : op 0 1 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) u4 q u9
    u5)
  have u11 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 0 1 (by decide)) u10 q
  have u12 : op 0 1 ≠ 2 := fun q => (cellUnique op 0 1 0 2 (by decide)) u10 q
  have u13 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u2 u11 q
    a1)
  have u14 : op 2 2 ≠ 1 := fun q => (chain op h.e677 0 2 1 2 1) u13 u7 q u12
  have u15 : op 2 2 ≠ 0 := fun q => (chain op h.e677 2 2 0 1 2) q u13 a6 a8
  exact (cellTotal (op 2 2)) u15 u14 a8 a0

theorem c1318 (op : Table) (h : Hyp op) :
    (op 3 2 = 0) → (op 1 1 ≠ 1) → (op 1 2 ≠ 2) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op
      3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a0
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a6
  have u2 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a6
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a6
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a4 a5 a6
  have u5 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a2 a4 a5 a6
  have u6 : op 1 0 ≠ 1 := fun q => (c1314 op h) q a2 a3 a4 a5 a6
  have u7 : op 2 0 ≠ 2 := fun q => (c1315 op h) q a3 u4 a5 a0
  have u8 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u7 q u4 a4)
  have u9 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q u8
  have u10 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 2 0 1 2) a0 q u8 u3
  have u11 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1317 op h) q u10 u6 a1 u5 a2 u8
    a3 u4 a5 a0 u1)
  have u12 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 2 3 (by decide)) q u11
  have u13 : op 2 0 ≠ 0 := fun q => (chain op h.e677 2 2 3 0 0) u11 a0 q u7
  have u14 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u13 q u7 u12)
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 2 1 2 3 1) u8 u11 q u9
  have u16 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u6 a1 q
    u15)
  have u17 : op 1 1 ≠ 0 := fun q => (chain op h.e677 1 2 1 0 1) u16 q u14 u5
  have u18 : op 1 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) u17 a1 u5 q)
  have u19 : op 3 1 ≠ 1 := fun q => (c1264 op h) u18 u15 q
  have u20 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 1) u18 q u16 a1
  exact (cellTotal (op 3 1)) u0 u19 u20 u2

theorem c1319 (op : Table) (h : Hyp op) :
    (op 2 1 = 2) → (op 1 0 ≠ 1) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 2 1 ≠ 3) → (op 2 2 ≠ 2) → (op
      2 3 ≠ 3) → (op 3 2 = 1) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q a0
  have u1 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 2 3 1 2) q a7 a0 a5
  have u2 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a8
  have u3 : op 2 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) q a4 u1 a6)
  have u4 : op 1 3 ≠ 1 := fun q => (chain op h.e677 3 2 1 1 2) a7 q a0 u2
  have u5 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) a1 a2 q u4)
  have u6 : op 1 2 ≠ 2 := fun q => (cellUnique op 1 2 1 2 (by decide)) u5 q
  have u7 : op 2 0 ≠ 1 := fun q => (cellUnique op 2 0 1 3 (by decide)) q u3
  have u8 : op 2 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 2) q u5 a0 a5
  have u9 : op 2 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 1) u7 u0 u8 q)
  have u10 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u8 a5 u1)
  have u11 : op 1 1 ≠ 3 := fun q => (chain op h.e677 1 2 1 3 1) u5 q u9 a3
  have u12 : op 1 0 ≠ 2 := fun q => (chain op h.e677 2 1 2 0 2) a0 u10 q u8
  have u13 : op 1 3 ≠ 2 := fun q => (chain op h.e677 1 3 2 2 1) q a0 a7 u11
  exact (rowTotal op h.surj 1 2) u12 a3 u6 u13

theorem c1320 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 1) → (op 1 2 ≠ 2) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a5
  have u1 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a5
  have u2 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a5
  have u3 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a3 a4 a5
  have u4 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a1 a3 a4 a5
  have u5 : op 3 2 ≠ 0 := fun q => (c1318 op h) q a0 a1 a2 a3 a4 a5
  have u6 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u5 q u2 u1)
  have u7 : op 1 0 ≠ 1 := fun q => (c1314 op h) q a1 a2 a3 a4 a5
  have u8 : op 2 1 ≠ 2 := fun q => (c1319 op h) q u7 a0 u4 a2 u3 a4 u6 a5
  have u9 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q u8 u3 a3)
  have u10 : op 2 0 ≠ 0 := fun q => (cellUnique op 2 0 0 2 (by decide)) q u9
  have u11 : op 2 0 ≠ 3 := fun q => (cellUnique op 2 0 2 3 (by decide)) u9 q
  have u12 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 2 1 0 2) u6 q u9 u2
  have u13 : op 2 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) u11 a2 q
    a4)
  have u14 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 2 3 1 1) u13 u6 q u8
  have u15 : op 0 3 ≠ 0 := fun q => (chain op h.e677 2 0 2 3 0) u9 u13 q u10
  have u16 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u14 u8 a2)
  have u17 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) u16 q
  have u18 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) u16 q
  have u19 : op 0 3 ≠ 2 := fun q => (chain op h.e677 2 0 2 3 2) u9 u13 q u17
  have u20 : op 0 3 ≠ 3 := fun q => (chain op h.e677 2 0 2 3 3) u9 u13 q u18
  have u21 : op 0 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u15 q u19 u20)
  have u22 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) q u21
  have u23 : op 1 3 ≠ 2 := fun q => (chain op h.e677 3 2 1 2 3) u6 q u13 u0
  have u24 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q u4 a1
    u23)
  have u25 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 2 (by decide)) q u24
  have u26 : op 0 0 ≠ 0 := fun q => (chain op h.e677 1 0 2 0 0) u24 u16 q u25
  have u27 : op 0 0 ≠ 3 := fun q => (chain op h.e677 1 0 2 0 3) u24 u16 q u12
  have u28 : op 0 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u26 u22 q u27)
  have u29 : op 1 2 = 0 := Classical.byContradiction (fun q => (chain op h.e677 1 0 2 0 2) u24 u16
    u28 q)
  have u30 : op 0 2 ≠ 0 := fun q => (chain op h.e677 0 0 2 2 0) u28 u9 q u26
  have u31 : op 0 1 ≠ 0 := fun q => (chain op h.e677 0 1 0 2 0) q u28 u29 u22
  exact (rowTotal op h.surj 0 0) u26 u31 u30 u15

theorem c1321 (op : Table) (h : Hyp op) :
    (op 2 1 ≠ 2) → (op 1 1 = 1) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 2 = 1) → (op
      3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a1
  have u1 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 3 (by decide)) q a6
  have u2 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a6
  have u3 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a3 a4 a6
  have u4 : op 3 2 ≠ 0 := fun q => (cellUnique op 3 2 0 1 (by decide)) q a5
  have u5 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q a5
  have u6 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q a0 u3 a3)
  have u7 : op 2 0 ≠ 0 := fun q => (cellUnique op 2 0 0 2 (by decide)) q u6
  have u8 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 2 1 0 2) a5 q u6 u2
  have u9 : op 2 0 ≠ 3 := fun q => (cellUnique op 2 0 2 3 (by decide)) u6 q
  have u10 : op 2 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 3) u9 a2 q
    a4)
  have u11 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 2 3 1 1) u10 a5 q a0
  have u12 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u11 a0 a2)
  have u13 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) u12 q
  have u14 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) u12 q
  have u15 : op 0 3 ≠ 3 := fun q => (chain op h.e677 2 0 2 3 3) u6 u10 q u14
  have u16 : op 0 3 ≠ 2 := fun q => (chain op h.e677 2 0 2 3 2) u6 u10 q u13
  have u17 : op 0 2 ≠ 2 := fun q => (chain op h.e677 0 2 2 2 3) q u6 u10 u16
  have u18 : op 0 3 ≠ 0 := fun q => (chain op h.e677 2 0 2 3 0) u6 u10 q u7
  have u19 : op 0 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u18 q u16 u15)
  have u20 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) q u19
  have u21 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 1 3 1 (by decide)) q u19
  have u22 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 1 1) q u19 a1 u5
  have u23 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u22 u4
    u1)
  have u24 : op 0 1 ≠ 2 := fun q => (chain op h.e677 3 0 0 1 2) u23 u19 q u4
  have u25 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 0 1 3) u23 u19 q u1
  have u26 : op 0 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 2) q u24 u17
    u16)
  have u27 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u21 u24 u25)
  have u28 : op 1 2 ≠ 0 := fun q => (chain op h.e677 0 1 0 2 0) u27 u26 q u20
  have u29 : op 1 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) q u0 u28
    u8)
  exact (chain op h.e677 1 0 0 0 2) u29 u27 u26 u28

theorem c1322 (op : Table) (h : Hyp op) :
    (op 3 2 = 1) → (op 1 2 ≠ 2) → (op 2 1 ≠ 3) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a3 a4 a5
  have u1 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a1 a3 a4 a5
  have u2 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1320 op h) q a1 a2 a3 a4 a5)
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u2 q
  have u4 : op 2 1 = 2 := Classical.byContradiction (fun q => (c1321 op h) q u2 a2 a3 a4 a0 a5)
  have u5 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q u4
  have u6 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 2 3 1 2) q a0 u4 u0
  have u7 : op 2 2 ≠ 1 := fun q => (chain op h.e677 2 1 2 1 1) u4 q u2 u5
  have u8 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u7 u0 u6)
  have u9 : op 1 0 ≠ 2 := fun q => (chain op h.e677 2 1 2 0 2) u4 u8 q u7
  have u10 : op 1 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u9 u1 a1
    q)
  exact (chain op h.e677 1 3 2 2 1) u10 u4 a0 u3

theorem c1323 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 3) → (op 0 3 ≠ 1) → (op 2 1 ≠ 3) → (op 2 2 ≠ 1) → (op 2 2 ≠ 2) → (op 2 3 ≠ 2) → (op
      2 3 ≠ 3) → (op 3 2 = 0) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q a3 a4 a0)
  have u1 : op 3 2 ≠ 1 := fun q => (cellUnique op 3 2 0 1 (by decide)) a7 q
  have u2 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a7 q
  have u3 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a7 q
  have u4 : op 2 0 ≠ 2 := fun q => (c1315 op h) q a2 a4 a6 a7
  have u5 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 2 0 (by decide)) q u0
  have u6 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) q u0
  have u7 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) u0 q
  have u8 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u4 q a4 a5)
  have u9 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u7 q a5 a6)
  have u10 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q u8
  have u11 : op 1 0 ≠ 2 := fun q => (chain op h.e677 2 1 2 0 2) u8 u0 q a3
  have u12 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 3 1 (by decide)) q u9
  have u13 : op 1 2 ≠ 2 := fun q => (chain op h.e677 1 2 2 2 0) q u8 u0 u11
  have u14 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u5 u12 u4 q)
  have u15 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 2 0 1 2) u0 q u8 a4
  have u16 : op 1 0 ≠ 0 := fun q => (chain op h.e677 2 1 2 0 0) u8 u0 q u12
  have u17 : op 1 0 ≠ 1 := fun q => (chain op h.e677 2 1 2 0 1) u8 u0 q u10
  have u18 : op 1 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u16 u17 u11 q)
  have u19 : op 0 0 ≠ 1 := fun q => (chain op h.e677 2 0 3 0 1) u14 a7 q u6
  have u20 : op 0 1 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u19 q u15
    a1)
  have u21 : op 1 3 ≠ 2 := fun q => (chain op h.e677 0 1 1 3 2) u20 u18 q u15
  have u22 : op 1 1 ≠ 0 := fun q => (c1259 op h) q u20 u17
  have u23 : op 1 3 ≠ 0 := fun q => (chain op h.e677 0 1 1 3 0) u20 u18 q u19
  have u24 : op 1 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u11 q u13
    u21)
  have u25 : op 1 2 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u16 u22 q
    u23)
  have u26 : op 3 3 ≠ 3 := fun q => (c1312 op h) u24 u13 a5 a6 q
  have u27 : op 3 0 ≠ 3 := fun q => (chain op h.e677 2 3 1 0 3) u9 u25 q a6
  have u28 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u3 q a8 u26)
  have u29 : op 3 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u27 q u2
    u26)
  exact (chain op h.e677 3 1 3 1 2) u29 u28 u24 u1

theorem c1324 (op : Table) (h : Hyp op) :
    (op 2 1 ≠ 3) → (op 1 2 ≠ 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a4
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a4
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a4
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a4
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a2 a3 a4
  have u5 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a1 a2 a3 a4
  have u6 : op 3 2 ≠ 1 := fun q => (c1322 op h) q a1 a0 a2 a3 a4
  have u7 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u6 u3 u2)
  have u8 : op 2 0 ≠ 2 := fun q => (c1315 op h) q a0 u4 a3 u7
  have u9 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u8 q u4 a2)
  have u10 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1320 op h) q a1 a0 a2 a3 a4)
  have u11 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u10
  have u12 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u10 q
  have u13 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 2 0 1 2) u7 q u9 u3
  have u14 : op 2 1 ≠ 1 := fun q => (cellUnique op 2 1 1 2 (by decide)) q u9
  have u15 : op 2 2 ≠ 1 := fun q => (chain op h.e677 2 1 2 1 1) u9 q u10 u14
  have u16 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1323 op h) q u13 a0 u15 u4 a2 a3
    u7 u1)
  have u17 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 2 3 (by decide)) q u16
  have u18 : op 2 0 ≠ 0 := fun q => (chain op h.e677 2 2 3 0 0) u16 u7 q u8
  have u19 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u18 q u8 u17)
  have u20 : op 1 3 ≠ 2 := fun q => (chain op h.e677 2 1 2 3 2) u9 u16 q u15
  have u21 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q u5 a1
    u20)
  have u22 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 2 3 (by decide)) u21 q
  have u23 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 2 2 1) u21 u9 q u11
  have u24 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 0 3 1 (by decide)) u19 q
  have u25 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u24 a2 a3)
  have u26 : op 0 2 ≠ 2 := fun q => (chain op h.e677 2 3 0 2 0) u25 q u7 u17
  have u27 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 2 (by decide)) q u21
  have u28 : op 0 2 ≠ 0 := fun q => (chain op h.e677 1 0 2 2 0) u21 u9 q u27
  have u29 : op 0 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u28 u23 u26 q)
  have u30 : op 3 0 ≠ 1 := fun q => (chain op h.e677 0 2 3 1 2) u29 q u9 u26
  have u31 : op 3 1 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u30 q u6
    u0)
  have u32 : op 1 2 ≠ 3 := fun q => (chain op h.e677 1 2 3 1 2) q u31 u9 a1
  have u33 : op 1 3 ≠ 3 := fun q => (c1277 op h) u31 q u0
  exact (rowTotal op h.surj 1 3) u22 u12 u32 u33

theorem c1325 (op : Table) (h : Hyp op) :
    (op 3 2 = 0) → (op 1 0 = 2) → (op 2 0 = 2) → (op 2 1 = 3) → (op 2 2 ≠ 2) → (op 3 3 ≠ 2) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 2 0 1 3) a0 q a3 a5
  have u1 : op 2 3 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) a2 q
  have u2 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 1 3 (by decide)) q a3
  have u3 : op 2 3 ≠ 3 := fun q => (rowUnique op h.inj 2 1 3 3 (by decide)) a3 q
  have u4 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) a1 q
  have u5 : op 2 0 ≠ 0 := fun q => (cellUnique op 2 0 0 2 (by decide)) q a2
  have u6 : op 2 2 = 1 := Classical.byContradiction (fun q => (chain op h.e677 2 1 3 0 2) a3 a0 a1
    q)
  have u7 : op 2 2 ≠ 0 := fun q => (cellUnique op 2 2 0 1 (by decide)) q u6
  have u8 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) u6 q
  have u9 : op 0 1 ≠ 2 := fun q => (chain op h.e677 2 0 2 1 2) a2 u6 q u7
  have u10 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 2 1 0 2) u6 q a2 a4
  have u11 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u8 u1 u3)
  have u12 : op 0 2 ≠ 2 := fun q => (chain op h.e677 2 3 0 2 0) u11 q a0 u2
  have u13 : op 1 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 3) u6 q a3 u1
  have u14 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u10 u13 u4 q)
  have u15 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 2 3) q a1 u14 u0
  have u16 : op 0 1 ≠ 0 := fun q => (chain op h.e677 2 0 2 1 0) a2 u6 q u5
  have u17 : op 0 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u16 u15 u9 q)
  have u18 : op 0 2 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) u17 q
  have u19 : op 0 2 ≠ 1 := fun q => (chain op h.e677 0 2 1 2 1) q a1 u6 u9
  have u20 : op 0 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) q u15 u19
    u0)
  have u21 : op 0 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) q u19 u12 u18)
  have u22 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q u20
  exact (chain op h.e677 0 0 1 2 0) u20 a1 u21 u22

theorem c1326 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a3
  have u1 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a3
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a3
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a3
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a1 a2 a3
  have u5 : op 1 1 ≠ 2 := fun q => (c1312 op h) q a0 a1 a2 a3
  have u6 : op 2 1 = 3 := Classical.byContradiction (fun q => (c1324 op h) q a0 a1 a2 a3)
  have u7 : op 2 1 ≠ 2 := fun q => (cellUnique op 2 1 2 3 (by decide)) q u6
  have u8 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q u7 u4 a1)
  have u9 : op 1 3 ≠ 2 := fun q => (c1304 op h) q u6 a3
  have u10 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q u5 a0
    u9)
  have u11 : op 3 2 ≠ 0 := fun q => (c1325 op h) q u10 u8 u6 u4 u0
  have u12 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u11 q u3 u2)
  have u13 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u12
  have u14 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 2 1 0 2) u12 q u8 u3
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 3 2 1 1 3) u12 q u6 u0
  have u16 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u14 u15 u9 q)
  have u17 : op 1 1 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) q u16
  have u18 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 2 3 3 (by decide)) q u16
  have u19 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 3 3 2 1) u16 q u12 u17
  have u20 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u19 u3
    u0)
  have u21 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u13 u19 u1)
  exact (chain op h.e677 1 3 3 0 2) u16 u21 u20 u18

theorem c1327 (op : Table) (h : Hyp op) :
    (op 2 1 = 3) → (op 1 2 = 2) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) q a1
  have u1 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q a1
  have u2 : op 2 3 ≠ 1 := fun q => (chain op h.e677 1 2 2 3 1) a1 a0 q u1
  have u3 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u2 a2 a3)
  exact (chain op h.e677 1 2 2 3 0) a1 a0 u3 u0

theorem c1328 (op : Table) (h : Hyp op) :
    (op 2 3 = 1) → (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 2 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) q a0
  have u1 : op 1 2 = 2 := Classical.byContradiction (fun q => (c1326 op h) q a1 a2 a3)
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a3
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a3
  have u4 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a1 a2 a3
  have u5 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) q u1
  have u6 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) u1 q
  have u7 : op 2 1 ≠ 3 := fun q => (c1327 op h) q u1 a1 a2
  have u8 : op 3 2 ≠ 1 := fun q => (chain op h.e677 2 3 1 2 1) a0 u1 q u7
  have u9 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u8 u3 u2)
  have u10 : op 2 0 ≠ 2 := fun q => (c1315 op h) q u7 u4 a2 u9
  have u11 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u10 q u4
    a1)
  have u12 : op 2 2 ≠ 3 := fun q => (chain op h.e677 1 2 2 2 3) u1 u11 q u6
  have u13 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u0 u4 u12)
  exact (chain op h.e677 1 2 2 2 0) u1 u11 u13 u5

theorem c1329 (op : Table) (h : Hyp op) :
    (op 2 3 ≠ 2) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2
  have u0 : op 1 2 = 2 := Classical.byContradiction (fun q => (c1326 op h) q a0 a1 a2)
  have u1 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q u0
  have u2 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) u0 q
  have u3 : op 2 1 ≠ 1 := fun q => (c1265 op h) u0 u1 q
  have u4 : op 2 3 ≠ 1 := fun q => (c1328 op h) q a0 a1 a2
  have u5 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u4 a0 a1)
  have u6 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q u5
  have u7 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) q u5
  have u8 : op 2 2 ≠ 2 := fun q => (c1306 op h) q a0 a1 a2
  have u9 : op 2 1 ≠ 3 := fun q => (c1327 op h) q u0 a0 a1
  have u10 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u6 u3 q u9)
  have u11 : op 2 2 ≠ 1 := fun q => (chain op h.e677 1 2 2 2 1) u0 u10 q u1
  have u12 : op 2 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) u7 u11 u8 q)
  exact (chain op h.e677 1 2 2 2 3) u0 u10 u12 u2

theorem c1330 (op : Table) (h : Hyp op) :
    (op 1 2 = 2) → (op 2 0 ≠ 2) → (op 2 1 ≠ 2) → (op 2 2 ≠ 2) → (op 2 2 ≠ 3) → (op 2 3 ≠ 0) → (op
      2 3 ≠ 1) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q a0
  have u1 : op 2 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) a1 a2 a3 q)
  have u2 : op 2 1 ≠ 1 := fun q => (c1265 op h) a0 u0 q
  have u3 : op 2 2 ≠ 1 := fun q => (c1270 op h) q a0 a2
  have u4 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u3 a3 a4)
  have u5 : op 2 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 1) q u2 u3 a6)
  have u6 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) q u4
  have u7 : op 0 2 ≠ 3 := fun q => (chain op h.e677 2 2 0 3 2) u4 q u1 a3
  have u8 : op 0 2 ≠ 2 := fun q => (c1269 op h) u4 q a1
  have u9 : op 0 2 ≠ 0 := fun q => (chain op h.e677 2 2 0 0 1) u4 q u5 a2
  have u10 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u9 q u8 u7)
  exact (chain op h.e677 2 0 1 2 1) u5 a0 u10 u6

theorem c1331 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 1) → (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a2
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a2
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a2
  have u3 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a2
  have u4 : op 2 3 = 2 := Classical.byContradiction (fun q => (c1329 op h) q a1 a2)
  have u5 : op 2 3 ≠ 0 := fun q => (cellUnique op 2 3 0 2 (by decide)) q u4
  have u6 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u4
  have u7 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q u4
  have u8 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) q u4
  have u9 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 3 2 3 3) u4 q a2 a1
  have u10 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q a0 u8 u9)
  have u11 : op 2 3 ≠ 1 := fun q => (cellUnique op 2 3 1 2 (by decide)) q u4
  have u12 : op 1 2 ≠ 2 := fun q => (c1330 op h) q u6 u7 u8 u9 u5 u11
  have u13 : op 3 0 ≠ 2 := fun q => (chain op h.e677 2 3 2 0 2) u4 u10 q u9
  have u14 : op 3 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) u13 q u3
    u1)
  have u15 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u14
  have u16 : op 0 2 ≠ 3 := fun q => (chain op h.e677 2 2 0 3 2) u10 q u4 u8
  have u17 : op 1 2 ≠ 3 := fun q => (chain op h.e677 3 1 2 2 3) u14 u4 q u0
  have u18 : op 1 2 ≠ 1 := fun q => (chain op h.e677 3 1 2 2 1) u14 u4 q u15
  have u19 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u18 u12 u17)
  have u20 : op 3 0 = 1 := Classical.byContradiction (fun q => (chain op h.e677 3 1 2 2 0) u14 u4
    u19 q)
  have u21 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 2 0 3 2) u19 q u4 u12
  have u22 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) u20 q
  have u23 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u22 u3 u2)
  have u24 : op 0 3 ≠ 3 := fun q => (chain op h.e677 0 3 3 1 2) q u20 u14 u16
  have u25 : op 0 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 3) q u21 u16
    u24)
  have u26 : op 2 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 2 3 2 0 1) u4 u10
    u20 q)
  have u27 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 2 0 1 3) u23 q u26 u1
  have u28 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 2 0 2 0) u23 q u10 u13
  have u29 : op 0 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) q u27 u28 u24)
  exact (chain op h.e677 0 3 0 3 3) u29 u25 a2 u24

theorem c1332 (op : Table) (h : Hyp op) :
    (op 2 1 = 3) → (op 0 2 ≠ 3) → (op 2 2 = 1) → (op 2 3 = 2) → (op 3 0 = 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 1 3 (by decide)) q a0
  have u1 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 1 2 3 (by decide)) a0 q
  have u2 : op 2 3 ≠ 3 := fun q => (rowUnique op h.inj 2 1 3 3 (by decide)) a0 q
  have u3 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 2 (by decide)) q a4
  have u4 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) a4 q
  have u5 : op 0 2 ≠ 0 := fun q => (chain op h.e677 3 0 2 2 0) a4 a3 q u3
  have u6 : op 2 3 ≠ 0 := fun q => (cellUnique op 2 3 0 2 (by decide)) q a3
  have u7 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q a3
  have u8 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q a3
  have u9 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) q a3
  have u10 : op 2 2 ≠ 0 := fun q => (cellUnique op 2 2 0 1 (by decide)) q a2
  have u11 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 2 1 (by decide)) q a2
  have u12 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) a2 q
  have u13 : op 3 1 ≠ 3 := fun q => (chain op h.e677 2 3 2 1 3) a3 a2 q u2
  have u14 : op 1 2 ≠ 3 := fun q => (chain op h.e677 2 2 1 3 2) a2 q a3 u9
  have u15 : op 2 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) q u11 u7 u0)
  have u16 : op 1 2 ≠ 2 := fun q => (c1330 op h) q u7 u8 u9 u1 u6 u12
  have u17 : op 0 2 ≠ 2 := fun q => (c1267 op h) u15 q u10
  have u18 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u5 q u17 a1)
  have u19 : op 1 0 ≠ 3 := fun q => (chain op h.e677 0 2 1 3 2) u18 q a3 u17
  have u20 : op 3 1 ≠ 0 := fun q => (chain op h.e677 2 3 2 1 0) a3 a2 q u0
  have u21 : op 3 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u20 q u4 u13)
  have u22 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) u21 q
  have u23 : op 1 3 ≠ 3 := fun q => (c1277 op h) u21 q u22
  have u24 : op 1 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u19 q u14
    u23)
  have u25 : op 1 2 ≠ 1 := fun q => (chain op h.e677 1 2 1 3 2) q u24 a3 u16
  have u26 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u25 u16 u14)
  exact (chain op h.e677 2 2 1 0 0) a2 u26 u15 u7

theorem c1333 (op : Table) (h : Hyp op) :
    (op 2 3 ≠ 3) → (op 3 3 = 3) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 3 (by decide)) q a1
  have u1 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a1
  have u2 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a1
  have u3 : op 2 3 = 2 := Classical.byContradiction (fun q => (c1329 op h) q a0 a1)
  have u4 : op 2 3 ≠ 0 := fun q => (cellUnique op 2 3 0 2 (by decide)) q u3
  have u5 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u3
  have u6 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q u3
  have u7 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) q u3
  have u8 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 3 3 (by decide)) q a1
  have u9 : op 2 2 = 1 := Classical.byContradiction (fun q => (c1331 op h) q a0 a1)
  have u10 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 2 1 (by decide)) q u9
  have u11 : op 2 1 ≠ 1 := fun q => (rowUnique op h.inj 2 1 2 1 (by decide)) q u9
  have u12 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) u9 q
  have u13 : op 1 2 ≠ 3 := fun q => (chain op h.e677 2 2 1 3 2) u9 q u3 u7
  have u14 : op 3 2 ≠ 2 := fun q => (c1289 op h) q a1
  have u15 : op 2 2 ≠ 3 := fun q => (chain op h.e677 2 3 2 3 3) u3 q a1 a0
  have u16 : op 1 2 ≠ 2 := fun q => (c1330 op h) q u5 u6 u7 u15 u4 u12
  have u17 : op 3 1 ≠ 2 := fun q => (chain op h.e677 2 3 2 1 2) u3 u9 q u15
  have u18 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u17 u14
    u2)
  have u19 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 2 (by decide)) q u18
  have u20 : op 3 0 ≠ 1 := fun q => (cellUnique op 3 0 1 2 (by decide)) q u18
  have u21 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 2 2 3) u18 u3 q u0
  have u22 : op 2 1 ≠ 3 := fun q => (c1332 op h) q u21 u9 u3 u18
  have u23 : op 3 1 ≠ 1 := fun q => (chain op h.e677 2 3 2 1 1) u3 u9 q u22
  have u24 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u11 u6 u22)
  have u25 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u23 u17 u8)
  have u26 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u20 u23 q
    u1)
  have u27 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 1 0 (by decide)) q u24
  have u28 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) u25 q
  have u29 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u27 u10 u5 q)
  have u30 : op 0 1 ≠ 3 := fun q => (chain op h.e677 2 0 3 1 3) u29 u26 q u4
  have u31 : op 0 2 ≠ 0 := fun q => (chain op h.e677 3 0 2 2 0) u18 u3 q u19
  have u32 : op 1 2 ≠ 1 := fun q => (chain op h.e677 2 2 1 1 0) u9 q u24 u5
  have u33 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u32 u16 u13)
  have u34 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 2 3 0 (by decide)) u33 q
  have u35 : op 1 3 ≠ 2 := fun q => (chain op h.e677 1 3 2 0 2) q u24 u18 u13
  have u36 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 0 2) q u25 u18 u13
  have u37 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u34 q u35 u36)
  have u38 : op 0 3 ≠ 3 := fun q => (chain op h.e677 0 3 3 2 1) q u18 u26 u30
  have u39 : op 0 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 3) q u30 u21
    u38)
  have u40 : op 0 0 ≠ 1 := fun q => (cellUnique op 0 0 1 3 (by decide)) q u39
  have u41 : op 0 2 ≠ 2 := fun q => (chain op h.e677 3 0 2 2 2) u18 u3 q u28
  have u42 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u31 q u41 u21)
  have u43 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) q u42
  have u44 : op 0 1 = 0 := Classical.byContradiction (fun q => (chain op h.e677 0 0 3 2 1) u39 u18
    u42 q)
  have u45 : op 0 1 ≠ 2 := fun q => (chain op h.e677 0 1 2 3 1) q u29 u37 u43
  have u46 : op 0 0 ≠ 2 := fun q => (chain op h.e677 0 1 0 2 0) u44 q u33 u40
  have u47 : op 0 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 2) u46 u45
    u41 q)
  exact (chain op h.e677 0 3 2 3 3) u47 u29 a1 u38

theorem c1334 (op : Table) (h : Hyp op) :
    (op 3 0 = 2) → (op 3 3 = 3) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 2 := fun q => (rowUnique op h.inj 3 0 3 2 (by decide)) a0 q
  have u1 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a1
  have u2 : op 2 3 = 3 := Classical.byContradiction (fun q => (c1333 op h) q a1)
  have u3 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q u2
  have u4 : op 3 2 ≠ 2 := fun q => (c1278 op h) q u2 u0
  have u5 : op 3 2 ≠ 0 := fun q => (chain op h.e677 2 3 3 0 2) u2 q a0 u3
  have u6 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u5 q u4 u1)
  have u7 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 2 (by decide)) q a0
  have u8 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 3 (by decide)) q a1
  have u9 : op 3 1 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u7 q u5 u8)
  have u10 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 3 3 (by decide)) q u2
  exact (chain op h.e677 2 3 3 1 0) u2 u6 u9 u10

theorem c1335 (op : Table) (h : Hyp op) :
    (op 3 3 = 3) → False := by
  intro a0
  have u0 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 3 (by decide)) q a0
  have u1 : op 3 3 ≠ 2 := fun q => (cellUnique op 3 3 2 3 (by decide)) q a0
  have u2 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 2 3 3 (by decide)) q a0
  have u3 : op 3 0 ≠ 2 := fun q => (c1334 op h) q a0
  have u4 : op 2 3 = 3 := Classical.byContradiction (fun q => (c1333 op h) q a0)
  have u5 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 3 3 (by decide)) q u4
  have u6 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q u4
  have u7 : op 3 2 ≠ 2 := fun q => (c1278 op h) q u4 u1
  have u8 : op 3 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) u3 q u7 u1)
  have u9 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u8
  have u10 : op 3 2 ≠ 1 := fun q => (chain op h.e677 2 3 3 1 2) u4 q u8 u6
  have u11 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u9 u10
    u0)
  have u12 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u10 u7 u2)
  exact (chain op h.e677 2 3 3 0 1) u4 u12 u11 u5

theorem c1336 (op : Table) (h : Hyp op) :
    (op 3 3 = 1) → (op 2 3 = 3) → (op 3 1 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q a0
  have u2 : op 3 1 ≠ 3 := fun q => (cellUnique op 3 1 2 3 (by decide)) a2 q
  have u3 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 3 3 (by decide)) q a1
  have u4 : op 1 3 ≠ 3 := fun q => (c1280 op h) a0 q u2
  have u5 : op 3 2 ≠ 3 := fun q => (chain op h.e677 2 3 3 3 1) a1 q a0 u3
  have u6 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u2 u5 u0)
  have u7 : op 1 3 ≠ 1 := fun q => (chain op h.e677 3 3 1 1 2) a0 q a2 u5
  have u8 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 3 1 0 3) a0 q u6 u0
  have u9 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u8 u7 q u4)
  exact (chain op h.e677 3 1 2 3 2) a2 a1 u9 u1

theorem c1337 (op : Table) (h : Hyp op) :
    (op 3 1 = 2) → (op 2 3 = 3) → (op 3 3 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) a0 q
  have u2 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q a1
  have u3 : op 3 3 ≠ 1 := fun q => (c1336 op h) q a1 a0
  have u4 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u3 a2 u0)
  have u5 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) q u4
  have u6 : op 3 2 ≠ 1 := fun q => (chain op h.e677 2 3 3 1 2) a1 q a0 u2
  have u7 : op 3 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u5 u6 u1 q)
  have u8 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u7 u4 q a2
  exact (chain op h.e677 2 3 3 3 0) a1 u7 u4 u8

theorem c1338 (op : Table) (h : Hyp op) :
    (op 3 3 = 0) → (op 2 3 = 3) → (op 3 0 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 3 0 (by decide)) q a0
  have u1 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a0
  have u2 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) q a0
  have u3 : op 3 0 ≠ 3 := fun q => (cellUnique op 3 0 2 3 (by decide)) a2 q
  have u4 : op 0 3 ≠ 3 := fun q => (c1279 op h) a0 q u3
  have u5 : op 0 3 ≠ 0 := fun q => (chain op h.e677 3 0 2 3 0) a2 a1 q u0
  have u6 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 0 2 3 1) a2 a1 q u1
  have u7 : op 0 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u5 u6 q u4)
  exact (chain op h.e677 3 0 2 3 2) a2 a1 u7 u2

theorem c1339 (op : Table) (h : Hyp op) :
    (op 3 3 ≠ 2) → (op 2 3 = 3) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q a1
  have u2 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 3 3 (by decide)) q a1
  have u3 : op 3 1 ≠ 2 := fun q => (c1337 op h) q a1 a0
  have u4 : op 3 2 ≠ 2 := fun q => (c1278 op h) q a1 a0
  have u5 : op 3 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 2) q u3 u4 a0)
  have u6 : op 3 3 ≠ 0 := fun q => (c1338 op h) q a1 u5
  have u7 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u6 q a0 u0)
  have u8 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u7
  have u9 : op 3 2 ≠ 0 := fun q => (chain op h.e677 2 3 3 0 2) a1 q u5 u1
  have u10 : op 3 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u9 u8 u4 q)
  exact (chain op h.e677 2 3 3 3 1) a1 u10 u7 u2

theorem c1340 (op : Table) (h : Hyp op) :
    (op 2 3 = 3) → False := by
  intro a0
  have u0 : op 2 2 ≠ 3 := fun q => (rowUnique op h.inj 2 2 3 3 (by decide)) q a0
  have u1 : op 3 3 = 2 := Classical.byContradiction (fun q => (c1339 op h) q a0)
  have u2 : op 3 2 = 3 := Classical.byContradiction (fun q => (c1281 op h) u1 a0 q)
  exact (chain op h.e677 2 3 3 3 2) a0 u2 u1 u0

theorem c1341 (op : Table) (h : Hyp op) :
    (op 3 2 = 3) → (op 2 2 ≠ 3) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q a0
  have u3 : op 3 0 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) q a0
  have u4 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 2 3 (by decide)) q a0
  have u5 : op 2 3 ≠ 2 := fun q => (chain op h.e677 3 3 2 2 3) a2 q a0 u0
  have u6 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a2
  have u7 : op 2 2 ≠ 2 := fun q => (chain op h.e677 3 2 3 2 2) a0 a2 q u2
  have u8 : op 2 2 ≠ 1 := fun q => (chain op h.e677 3 2 3 2 1) a0 a2 q u6
  have u9 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u8 u7 a1)
  have u10 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) u9 q
  have u11 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u10 q u5 u1)
  have u12 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 3 2 1 0) a2 u11 q u3
  have u13 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 3 2 1 1) a2 u11 q u4
  exact (cellTotal (op 3 1)) u12 u13 u6 u4

theorem c1342 (op : Table) (h : Hyp op) :
    (op 0 3 = 1) → (op 2 1 ≠ 2) → (op 2 1 ≠ 3) → (op 3 2 = 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 3 2 (by decide)) q a4
  have u1 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a4
  have u2 : op 2 1 ≠ 0 := fun q => (chain op h.e677 3 2 0 1 0) a3 a0 q u0
  have u3 : op 2 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u2 q a1 a2)
  exact (chain op h.e677 3 2 0 1 1) a3 a0 u3 u1

theorem c1344 (op : Table) (h : Hyp op) :
    (op 2 3 = 1) → (op 3 1 ≠ 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 3 2 1 3) a2 a0 q u0
  have u2 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a2
  have u3 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 3 2 1 1) a2 a0 q u1
  exact (cellTotal (op 3 1)) a1 u3 u2 u1

theorem c1345 (op : Table) (h : Hyp op) :
    (op 2 1 ≠ 3) → (op 0 3 ≠ 2) → (op 0 3 ≠ 3) → (op 2 1 ≠ 0) → (op 2 1 ≠ 2) → (op 2 2 ≠ 0) → (op
      2 2 ≠ 3) → (op 3 2 = 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 2 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) a3 q a4 a0)
  have u3 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 2 (by decide)) q a8
  have u4 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a7 q
  have u5 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a7
  have u6 : op 2 3 ≠ 1 := fun q => (c1344 op h) q u5 a8
  have u7 : op 0 3 ≠ 1 := fun q => (c1342 op h) q a4 a0 a7 a8
  have u8 : op 0 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) q u7 a1 a2)
  have u9 : op 3 2 ≠ 1 := fun q => (cellUnique op 3 2 0 1 (by decide)) a7 q
  have u10 : op 2 2 ≠ 1 := fun q => (rowUnique op h.inj 2 1 2 1 (by decide)) u2 q
  have u11 : op 2 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) a5 u10 q a6)
  have u12 : op 2 3 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) u11 q
  have u13 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u6 u12 u1)
  have u14 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 2 0 3) a8 u13 q u0
  have u15 : op 3 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u14 q u4
    u0)
  have u16 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 3 (by decide)) q u15
  have u17 : op 1 2 ≠ 3 := fun q => (chain op h.e677 3 1 3 2 3) u15 a8 q u3
  have u18 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 2) q u15 a8 u17
  have u19 : op 1 2 ≠ 1 := fun q => (chain op h.e677 3 1 3 2 1) u15 a8 q u16
  have u20 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 3 0 1 3) u13 q u15 u1
  have u21 : op 0 0 ≠ 1 := fun q => (chain op h.e677 0 3 0 1 3) u8 q u15 a2
  have u22 : op 1 2 ≠ 2 := fun q => (chain op h.e677 3 1 3 2 2) u15 a8 q u9
  have u23 : op 1 1 ≠ 2 := fun q => (c1263 op h) q u19 u2
  have u24 : op 0 1 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u21 q u20
    u7)
  have u25 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u19 u22 u17)
  have u26 : op 1 0 ≠ 0 := fun q => (c1255 op h) u24 u21 q
  have u27 : op 1 0 ≠ 2 := fun q => (chain op h.e677 0 1 1 2 0) u24 q u25 u21
  have u28 : op 1 0 ≠ 3 := fun q => (chain op h.e677 1 0 3 3 0) q u15 u8 u26
  have u29 : op 1 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u27 u23
    u22 q)
  have u30 : op 1 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u28 q u17
    u18)
  exact (chain op h.e677 1 1 3 3 2) u30 u15 u29 u19

theorem c1346 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 0) → (op 2 2 ≠ 1) → (op 2 2 ≠ 3) → (op 3 2 = 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 2 (by decide)) q a4
  have u3 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 3 2 (by decide)) q a4
  have u4 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a4
  have u5 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a3 q
  have u6 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 2 0 (by decide)) q a3
  have u7 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a3
  have u8 : op 2 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) a0 a1 q a2)
  have u9 : op 2 3 ≠ 1 := fun q => (c1344 op h) q u7 a4
  have u10 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 2 2 (by decide)) q u8
  have u11 : op 2 3 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) u8 q
  have u12 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u9 u11 u1)
  have u13 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q u12
  have u14 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 2 0 3) a4 u12 q u0
  have u15 : op 3 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u14 q u5
    u0)
  have u16 : op 3 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u6 q u3 u14)
  have u17 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 3 (by decide)) q u15
  have u18 : op 1 2 ≠ 3 := fun q => (chain op h.e677 3 1 3 2 3) u15 a4 q u2
  have u19 : op 1 2 ≠ 1 := fun q => (chain op h.e677 3 1 3 2 1) u15 a4 q u17
  have u20 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) u16 q
  have u21 : op 1 2 ≠ 2 := fun q => (chain op h.e677 3 1 3 2 2) u15 a4 q u20
  have u22 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u19 u21 u18)
  have u23 : op 1 1 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) q u22
  have u24 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 2 0 2 2) a3 q u8 u4
  have u25 : op 0 3 ≠ 3 := fun q => (chain op h.e677 3 2 0 3 0) a3 q u12 u3
  have u26 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 2) q u15 a4 u18
  have u27 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 2 3 0 (by decide)) u22 q
  have u28 : op 2 1 = 3 := Classical.byContradiction (fun q => (c1345 op h) q u24 u25 u13 u10 a0
    a2 a3 a4)
  have u29 : op 1 3 ≠ 2 := fun q => (chain op h.e677 1 3 2 3 2) q u28 a4 u18
  have u30 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u27 q u29 u26)
  have u31 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) q u30
  have u32 : op 1 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 1) q u15 u30 u31
  have u33 : op 1 1 ≠ 2 := fun q => (chain op h.e677 1 1 2 3 1) q u28 u30 u31
  exact (cellTotal (op 1 1)) u23 u31 u33 u32

theorem c1347 (op : Table) (h : Hyp op) :
    (op 2 2 = 0) → (op 3 2 = 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a1
  have u2 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 2 3 0 (by decide)) a0 q
  have u3 : op 2 3 ≠ 1 := fun q => (c1344 op h) q u1 a2
  have u4 : op 2 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u2 u3 q u0)
  have u5 : op 3 0 ≠ 3 := fun q => (chain op h.e677 2 3 2 0 3) u4 a0 q u0
  exact (chain op h.e677 3 3 2 2 0) a2 u4 a1 u5

theorem c1348 (op : Table) (h : Hyp op) :
    (op 2 3 ≠ 0) → (op 2 2 = 1) → (op 3 2 = 0) → (op 3 3 = 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 2 2 ≠ 0 := fun q => (cellUnique op 2 2 0 1 (by decide)) q a1
  have u3 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 2 1 (by decide)) q a1
  have u4 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 2 (by decide)) q a3
  have u5 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a3
  have u6 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a2 q
  have u7 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a2
  have u8 : op 2 3 ≠ 1 := fun q => (rowUnique op h.inj 2 2 3 1 (by decide)) a1 q
  have u9 : op 2 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) a0 u8 q u1)
  have u10 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u9
  have u11 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 2 0 (by decide)) q a2
  have u12 : op 3 1 ≠ 3 := fun q => (chain op h.e677 2 3 2 1 3) u9 a1 q u1
  have u13 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u12 u6
    u0)
  have u14 : op 3 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u7 q u5 u12)
  have u15 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 3 2 3) u13 a3 q u4
  have u16 : op 0 2 ≠ 0 := fun q => (chain op h.e677 3 0 3 2 0) u13 a3 q u11
  have u17 : op 0 2 ≠ 1 := fun q => (chain op h.e677 3 0 3 2 1) u13 a3 q u7
  have u18 : op 0 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u16 u17 q u15)
  have u19 : op 2 0 ≠ 0 := fun q => (c1267 op h) q u18 u2
  have u20 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u19 u3 u10 q)
  have u21 : op 2 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 2 3 2 1 1) u9 a1
    u14 q)
  exact (rowUnique op h.inj 2 0 1 3 (by decide)) u20 u21

theorem c1349 (op : Table) (h : Hyp op) :
    (op 3 2 ≠ 1) → (op 2 2 ≠ 3) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 3 := fun q => (c1341 op h) q a1 a2
  have u2 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a2
  have u3 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q a0 u2 u1)
  have u4 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 1 2 (by decide)) q a2
  have u5 : op 2 2 ≠ 0 := fun q => (c1347 op h) q u3 a2
  have u6 : op 2 2 = 1 := Classical.byContradiction (fun q => (c1346 op h) u5 q a1 u3 a2)
  have u7 : op 2 2 ≠ 2 := fun q => (cellUnique op 2 2 1 2 (by decide)) u6 q
  have u8 : op 2 0 ≠ 1 := fun q => (rowUnique op h.inj 2 0 2 1 (by decide)) q u6
  have u9 : op 2 3 = 0 := Classical.byContradiction (fun q => (c1348 op h) q u6 u3 a2)
  have u10 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) q u9
  have u11 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 2 0 3) a2 u9 q u0
  have u12 : op 3 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u11 q u1
    u0)
  have u13 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 3 (by decide)) q u12
  have u14 : op 1 2 ≠ 3 := fun q => (chain op h.e677 3 1 3 2 3) u12 a2 q u4
  have u15 : op 1 2 ≠ 1 := fun q => (chain op h.e677 3 1 3 2 1) u12 a2 q u13
  have u16 : op 2 3 ≠ 2 := fun q => (cellUnique op 2 3 0 2 (by decide)) u9 q
  have u17 : op 1 2 ≠ 2 := fun q => (chain op h.e677 3 1 3 2 2) u12 a2 q a0
  have u18 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u15 u17 u14)
  have u19 : op 2 0 ≠ 2 := fun q => (chain op h.e677 2 2 1 0 2) u6 u18 q u7
  have u20 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u10 u8 u19 q)
  exact (chain op h.e677 2 2 1 0 3) u6 u18 u20 u16

theorem c1350 (op : Table) (h : Hyp op) :
    (op 2 3 = 0) → (op 3 0 ≠ 1) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 2 0 3) a2 a0 q u0
  have u2 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 3 2 0 0) a2 a0 q u1
  have u3 : op 3 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u2 a1 q u1)
  exact (rowUnique op h.inj 3 0 3 2 (by decide)) u3 a2

theorem c1351 (op : Table) (h : Hyp op) :
    (op 3 1 = 3) → (op 2 2 ≠ 3) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 3 (by decide)) q a0
  have u3 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1349 op h) q a1 a2)
  have u4 : op 2 3 ≠ 1 := fun q => (chain op h.e677 3 3 2 1 3) a2 q a0 u0
  have u5 : op 3 0 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) q u3
  have u6 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u3 q
  have u7 : op 2 3 ≠ 0 := fun q => (c1350 op h) q u5 a2
  have u8 : op 2 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u7 u4 q u1)
  have u9 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u8
  have u10 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q u8
  have u11 : op 1 2 ≠ 3 := fun q => (chain op h.e677 3 1 3 2 3) a0 a2 q u6
  have u12 : op 1 2 ≠ 1 := fun q => (chain op h.e677 3 1 3 2 1) a0 a2 q u2
  have u13 : op 1 2 ≠ 0 := fun q => (chain op h.e677 3 1 3 2 0) a0 a2 q u5
  have u14 : op 1 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u13 u12 q u11)
  have u15 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 2 3 2 (by decide)) q u8
  exact (c1330 op h) u14 u9 u10 u15 a1 u7 u4

theorem c1352 (op : Table) (h : Hyp op) :
    (op 1 2 = 2) → (op 2 3 = 1) → (op 2 3 ≠ 2) → (op 3 2 = 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) q a0
  have u1 : op 2 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 2 3 1 2 1) a1 a0 a3
    q)
  exact (chain op h.e677 1 2 2 3 1) a0 u1 a1 u0

theorem c1354 (op : Table) (h : Hyp op) :
    (op 2 2 ≠ 3) → (op 3 3 = 2) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a1
  have u3 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 2 (by decide)) q a1
  have u4 : op 3 1 ≠ 3 := fun q => (c1351 op h) q a0 a1
  have u5 : op 3 2 ≠ 3 := fun q => (c1341 op h) q a0 a1
  have u6 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u4 u5 u0)
  have u7 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 3 (by decide)) q u6
  have u8 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 3 2 3) u6 a1 q u3
  have u9 : op 0 2 ≠ 0 := fun q => (chain op h.e677 3 0 3 2 0) u6 a1 q u7
  have u10 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1349 op h) q a0 a1)
  have u11 : op 3 0 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) q u10
  have u12 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u10
  have u13 : op 2 3 ≠ 0 := fun q => (c1350 op h) q u11 a1
  have u14 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u12 u2 u4)
  have u15 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) u14 q
  have u16 : op 0 2 ≠ 2 := fun q => (chain op h.e677 3 0 3 2 2) u6 a1 q u15
  have u17 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u9 q u16 u8)
  have u18 : op 2 3 ≠ 2 := fun q => (chain op h.e677 3 3 2 2 1) a1 q u10 u4
  have u19 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u13 q u18 u1)
  have u20 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 3 1 0 3) u19 q u6 u1
  have u21 : op 0 3 ≠ 3 := fun q => (chain op h.e677 0 3 3 3 2) q u6 a1 u8
  have u22 : op 1 2 ≠ 2 := fun q => (c1352 op h) q u19 u18 u10
  have u23 : op 0 3 ≠ 1 := fun q => (rowUnique op h.inj 0 2 3 1 (by decide)) u17 q
  have u24 : op 1 2 ≠ 3 := fun q => (chain op h.e677 2 3 1 3 2) u19 q a1 a0
  have u25 : op 1 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u20 q u22 u24)
  have u26 : op 2 0 = 3 := Classical.byContradiction (fun q => (chain op h.e677 2 3 1 1 0) u19 u25
    u14 q)
  have u27 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 1 0 2 1) u14 q u25 u12
  have u28 : op 0 1 ≠ 3 := fun q => (chain op h.e677 2 0 3 1 3) u26 u10 q u13
  have u29 : op 0 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) q u23 u27 u21)
  have u30 : op 0 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 3) q u28 u8
    u21)
  have u31 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 3 0 (by decide)) q u29
  exact (chain op h.e677 0 0 3 3 0) u30 u6 u29 u31

theorem c1355 (op : Table) (h : Hyp op) :
    (op 2 3 = 1) → (op 1 2 ≠ 2) → (op 2 3 ≠ 2) → (op 3 3 = 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 3 2 1 3) a3 a0 q u0
  have u3 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 3 2 1 1) a3 a0 q u2
  have u4 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a3
  have u5 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a3
  have u6 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1354 op h) q a3)
  have u7 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u3 u4 u2)
  have u8 : op 2 2 ≠ 2 := fun q => (cellUnique op 2 2 2 3 (by decide)) q u6
  have u9 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 2 3 (by decide)) q u6
  have u10 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 1 0 (by decide)) q u7
  have u11 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) u7 q
  have u12 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) u7 q
  have u13 : op 1 2 ≠ 1 := fun q => (chain op h.e677 2 3 1 1 0) a0 q u7 u9
  have u14 : op 3 0 = 3 := Classical.byContradiction (fun q => (chain op h.e677 3 3 2 1 0) a3 a0
    u7 q)
  have u15 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) u14 q
  have u16 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 3 1 0 3) a0 q u14 u1
  have u17 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u11 q u5 u15)
  have u18 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u16 u13 a1 q)
  have u19 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 2 3 3 (by decide)) u18 q
  have u20 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 3 2 3) u14 a3 q u12
  have u21 : op 0 2 ≠ 2 := fun q => (chain op h.e677 3 0 3 2 2) u14 a3 q u11
  have u22 : op 0 2 ≠ 0 := fun q => (chain op h.e677 3 0 3 2 0) u14 a3 q u10
  have u23 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u22 q u21 u20)
  have u24 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) q u23
  have u25 : op 2 1 ≠ 2 := fun q => (chain op h.e677 2 2 3 1 2) u6 u17 q u8
  have u26 : op 2 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) q u25 u8
    a2)
  have u27 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 2 1 0 2) u17 q u26 u5
  have u28 : op 1 0 ≠ 0 := fun q => (chain op h.e677 0 2 1 0 2) u23 q u26 u21
  have u29 : op 1 1 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u28 q u16
    u27)
  have u30 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 0 1 (by decide)) u29 q
  have u31 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 0 3) q u29 u14 u19
  have u32 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u30 u13
    u31)
  have u33 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u27 u31 q u19)
  have u34 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 1 0 2 3) u29 q u18 u31
  have u35 : op 0 1 ≠ 0 := fun q => (chain op h.e677 1 1 0 0 1) u29 q u32 u30
  have u36 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 2) u29 q u33 u13
  exact (cellTotal (op 0 1)) u35 u24 u34 u36

theorem c1356 (op : Table) (h : Hyp op) :
    (op 2 3 = 0) → (op 2 3 ≠ 2) → (op 3 3 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a2
  have u2 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1354 op h) q a2)
  have u3 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 2 3 (by decide)) q u2
  have u4 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 2 3 (by decide)) q u2
  have u5 : op 3 0 = 1 := Classical.byContradiction (fun q => (c1350 op h) a0 q a2)
  have u6 : op 2 2 ≠ 2 := fun q => (cellUnique op 2 2 2 3 (by decide)) q u2
  have u7 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 0 2 1 (by decide)) u5 q
  have u8 : op 3 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 3 3 2 0 1) a2 a0 u5
    q)
  have u9 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 1 2 3 (by decide)) u8 q
  have u10 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 3 0 1 3) a0 q u8 u0
  have u11 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u7 u1 u9)
  have u12 : op 0 2 ≠ 0 := fun q => (chain op h.e677 2 3 0 0 1) a0 q u5 u4
  have u13 : op 2 0 ≠ 2 := fun q => (c1315 op h) q u4 u6 u0 u11
  have u14 : op 2 1 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u13 q u6
    a1)
  have u15 : op 0 2 ≠ 2 := fun q => (chain op h.e677 2 3 0 2 0) a0 q u11 u3
  have u16 : op 0 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u12 u10 u15 q)
  exact (chain op h.e677 0 2 3 1 2) u16 u5 u14 u15

theorem c1357 (op : Table) (h : Hyp op) :
    (op 2 3 ≠ 2) → (op 3 3 = 2) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a1
  have u3 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1354 op h) q a1)
  have u4 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 2 3 (by decide)) q u3
  have u5 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 3 2 (by decide)) q a1
  have u6 : op 2 3 ≠ 0 := fun q => (c1356 op h) q a0 a1
  have u7 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u6 q a0 u1)
  have u8 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 3 2 1 3) a1 u7 q u0
  have u9 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 3 2 1 1) a1 u7 q u8
  have u10 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u9 u5 u8)
  have u11 : op 3 2 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) u10 q
  have u12 : op 1 2 = 2 := Classical.byContradiction (fun q => (c1355 op h) u7 q a0 a1)
  have u13 : op 3 2 ≠ 3 := fun q => (chain op h.e677 2 3 1 2 3) u7 u12 q u1
  have u14 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u11 q u2 u13)
  exact (chain op h.e677 2 3 1 2 1) u7 u12 u14 u4

theorem c1359 (op : Table) (h : Hyp op) :
    (op 3 2 = 1) → (op 3 3 = 2) → False := by
  intro a0 a1
  have u0 : op 2 3 = 2 := Classical.byContradiction (fun q => (c1357 op h) q a1)
  have u1 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1354 op h) q a1)
  have u2 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u0
  have u3 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q u0
  have u4 : op 2 1 ≠ 3 := fun q => (rowUnique op h.inj 2 1 2 3 (by decide)) q u1
  have u5 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 2 3 1 1) u1 a0 q u3
  have u6 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u5 u3 u4)
  exact (chain op h.e677 2 2 3 1 0) u1 a0 u6 u2

theorem c1360 (op : Table) (h : Hyp op) :
    (op 3 3 = 2) → False := by
  intro a0
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 2 3 2 (by decide)) q a0
  have u2 : op 3 2 ≠ 1 := fun q => (c1359 op h) q a0
  have u3 : op 2 3 = 2 := Classical.byContradiction (fun q => (c1357 op h) q a0)
  have u4 : op 2 2 = 3 := Classical.byContradiction (fun q => (c1354 op h) q a0)
  have u5 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 2 2 3) a0 u3 q u0
  have u6 : op 3 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) q u2 u1 u5)
  have u7 : op 2 0 ≠ 2 := fun q => (rowUnique op h.inj 2 0 3 2 (by decide)) q u3
  have u8 : op 2 1 ≠ 2 := fun q => (rowUnique op h.inj 2 1 3 2 (by decide)) q u3
  have u9 : op 2 0 ≠ 3 := fun q => (rowUnique op h.inj 2 0 2 3 (by decide)) q u4
  have u10 : op 2 0 ≠ 0 := fun q => (chain op h.e677 2 2 3 0 0) u4 u6 q u7
  have u11 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u10 q u7 u9)
  exact (chain op h.e677 2 2 3 0 1) u4 u6 u11 u8

theorem c1361 (op : Table) (h : Hyp op) :
    (op 1 3 = 0) → (op 3 2 = 0) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a1 q
  have u3 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a1 q
  have u4 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u3 q u1 u0)
  have u5 : op 3 0 ≠ 1 := fun q => (rowUnique op h.inj 3 0 3 1 (by decide)) q u4
  have u6 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 1 0 3) u4 a0 q u0
  have u7 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 3 1 0 0) u4 a0 q u6
  have u8 : op 3 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u7 u5 q u6)
  exact (chain op h.e677 3 3 1 0 2) u4 a0 u8 u2

theorem c1362 (op : Table) (h : Hyp op) :
    (op 3 0 ≠ 3) → (op 3 2 = 0) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a1 q
  have u3 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u2 q u1 u0)
  have u4 : op 3 0 ≠ 1 := fun q => (rowUnique op h.inj 3 0 3 1 (by decide)) q u3
  have u5 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u3
  have u6 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u3
  have u7 : op 1 3 ≠ 2 := fun q => (chain op h.e677 3 3 1 2 0) u3 q a1 a0
  have u8 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 0 3 (by decide)) a1 q
  have u9 : op 3 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) a0 q u8 u0)
  have u10 : op 1 1 ≠ 2 := fun q => (chain op h.e677 3 1 3 1 2) u9 u3 q u6
  have u11 : op 1 3 ≠ 0 := fun q => (c1361 op h) q a1
  have u12 : op 1 1 ≠ 1 := fun q => (chain op h.e677 3 1 3 1 1) u9 u3 q u5
  have u13 : op 1 1 ≠ 0 := fun q => (chain op h.e677 3 1 3 1 0) u9 u3 q u4
  have u14 : op 1 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) u13 u12 u10 q)
  have u15 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) u14 q
  have u16 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 1 3 3 1) u14 u9 q u12
  exact (cellTotal (op 1 3)) u11 u16 u7 u15

theorem c1364 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 1) → (op 1 1 ≠ 3) → (op 3 2 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a2
  have u3 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a2 q
  have u4 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1362 op h) q a2)
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u3 q u1 u0)
  have u6 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 3 (by decide)) q u4
  have u7 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 0 1 3 (by decide)) u4 q
  have u8 : op 3 2 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) u4 q
  have u9 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) u4 u5 q u3
  have u10 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 3 1 0) u4 u5 q u6
  have u11 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 3 1 0 3) u5 q u4 u0
  have u12 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u5
  have u13 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u2 u12 q u7)
  have u14 : op 1 3 ≠ 3 := fun q => (c1280 op h) u5 q u7
  have u15 : op 0 1 ≠ 1 := fun q => (chain op h.e677 3 0 3 1 1) u4 u5 q u2
  have u16 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u10 u15 q u9)
  have u17 : op 1 3 ≠ 1 := fun q => (chain op h.e677 3 3 1 1 2) u5 q u13 u8
  have u18 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u11 u17 q u14)
  have u19 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) q u18
  have u20 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q u18
  have u21 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q a0 u19 a1)
  have u22 : op 1 2 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) u21 q
  have u23 : op 1 2 ≠ 3 := fun q => (chain op h.e677 1 1 0 2 3) u21 u16 q u17
  have u24 : op 1 2 ≠ 1 := fun q => (chain op h.e677 1 1 0 2 1) u21 u16 q a0
  exact (cellTotal (op 1 2)) u22 u24 u20 u23

theorem c1365 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 3) → (op 1 1 = 1) → (op 3 2 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a2
  have u3 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a2 q
  have u4 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1362 op h) q a2)
  have u5 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a1
  have u6 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) a1 q
  have u7 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a1 q
  have u8 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u3 q u1 u0)
  have u9 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 3 (by decide)) q u4
  have u10 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 0 1 3 (by decide)) u4 q
  have u11 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) u4 u8 q u3
  have u12 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 3 1 0) u4 u8 q u9
  have u13 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 3 1 0 3) u8 q u4 u0
  have u14 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u8
  have u15 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u2 u14 q u10)
  have u16 : op 1 3 ≠ 3 := fun q => (c1280 op h) u8 q u10
  have u17 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u13 u7 q u16)
  have u18 : op 1 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) q u6 a0
    u16)
  have u19 : op 0 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 1) q u18 u8 u11
  have u20 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 3 2 1) u18 u15 q u5
  have u21 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 3 2) q u18 u17 u20
  have u22 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u12 u21 q u11)
  have u23 : op 0 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) q u21 u20
    u19)
  have u24 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 1 3 2 (by decide)) u22 q
  have u25 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q u23
  have u26 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 0 1 3 0) u23 u18 q u25
  have u27 : op 0 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u26 u19 u24 q)
  exact (chain op h.e677 0 3 3 3 1) u27 u4 u8 u11

theorem c1366 (op : Table) (h : Hyp op) :
    (op 1 1 = 1) → (op 3 2 = 0) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a0
  have u3 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a1 q
  have u4 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1362 op h) q a1)
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u3 q u1 u0)
  have u6 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 3 (by decide)) q u4
  have u7 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) u4 u5 q u3
  have u8 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 3 1 0) u4 u5 q u6
  have u9 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 3 1 0 3) u5 q u4 u0
  have u10 : op 1 2 = 3 := Classical.byContradiction (fun q => (c1365 op h) q a0 a1)
  have u11 : op 1 2 ≠ 0 := fun q => (cellUnique op 1 2 0 3 (by decide)) q u10
  have u12 : op 1 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) q u2 u11
    u9)
  have u13 : op 0 1 ≠ 1 := fun q => (c1258 op h) u12 q u2
  have u14 : op 0 0 ≠ 1 := fun q => (c1252 op h) q u8 u12
  have u15 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u8 u13 q u7)
  have u16 : op 0 2 ≠ 1 := fun q => (chain op h.e677 1 0 0 2 1) u12 u15 q u2
  have u17 : op 0 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u14 u13
    u16 q)
  have u18 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 1 3 (by decide)) u17 q
  exact (chain op h.e677 0 3 1 0 3) u17 u12 u4 u18

theorem c1367 (op : Table) (h : Hyp op) :
    (op 3 2 = 0) → False := by
  intro a0
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u3 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 2 0 (by decide)) q a0
  have u4 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 2 3 0 (by decide)) a0 q
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u4 q u2 u0)
  have u6 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u5
  have u7 : op 1 1 ≠ 1 := fun q => (c1366 op h) q a0
  have u8 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1362 op h) q a0)
  have u9 : op 3 0 ≠ 1 := fun q => (rowUnique op h.inj 3 0 3 1 (by decide)) q u5
  have u10 : op 1 1 = 3 := Classical.byContradiction (fun q => (c1364 op h) u7 q a0)
  have u11 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) u10 q
  have u12 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 0 1 3 (by decide)) u8 q
  have u13 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u3 u6 q u12)
  have u14 : op 1 2 ≠ 1 := fun q => (chain op h.e677 1 1 3 2 1) u10 u13 q u7
  have u15 : op 1 2 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 2) u10 u13 q u14
  have u16 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u14 u15 u11)
  have u17 : op 1 0 = 1 := Classical.byContradiction (fun q => (chain op h.e677 1 1 3 2 0) u10 u13
    u16 q)
  have u18 : op 2 3 ≠ 2 := fun q => (chain op h.e677 3 1 2 2 0) u13 q u16 u9
  have u19 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 1 2 0 1) u13 q u17 u6
  have u20 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u19 q u18 u1)
  exact (chain op h.e677 2 3 1 0 3) u20 u16 u8 u1

theorem c1368 (op : Table) (h : Hyp op) :
    (op 1 0 = 1) → (op 0 3 ≠ 2) → (op 1 1 = 3) → (op 1 3 ≠ 0) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) a0 q
  have u2 : op 1 2 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) a0 q
  have u3 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) a0 q
  have u4 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 1 3 0 1) a2 q a0 u1
  have u5 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 3 (by decide)) q a2
  have u6 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) a2 q
  have u7 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) a2 q
  have u8 : op 1 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) a3 u3 q u7)
  have u9 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q u8
  have u10 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u2 u9 u6)
  have u11 : op 1 0 ≠ 0 := fun q => (rowUnique op h.inj 1 0 2 0 (by decide)) q u10
  have u12 : op 0 3 ≠ 1 := fun q => (chain op h.e677 1 0 1 3 1) a0 a2 q u5
  have u13 : op 0 3 ≠ 0 := fun q => (chain op h.e677 1 0 1 3 0) a0 a2 q u11
  have u14 : op 0 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u13 u12 a1 q)
  have u15 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 3 3 (by decide)) q u14
  have u16 : op 3 0 ≠ 0 := fun q => (c1257 op h) u14 u15 q
  have u17 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u16 u4 u0
    q)
  have u18 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1279 op h) u17 u14 q)
  exact (chain op h.e677 0 3 3 3 0) u14 u18 u17 u15

theorem c1369 (op : Table) (h : Hyp op) :
    (op 1 3 = 2) → (op 0 3 ≠ 2) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 1 1 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 1 3 ≠ 1 := fun q => (cellUnique op 1 3 1 2 (by decide)) q a0
  have u2 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q a0
  have u3 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q a0
  have u4 : op 1 3 ≠ 0 := fun q => (cellUnique op 1 3 0 2 (by decide)) q a0
  have u5 : op 1 0 ≠ 1 := fun q => (c1368 op h) q a1 a4 u4
  have u6 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u5 a2 q u1)
  have u7 : op 2 3 ≠ 2 := fun q => (chain op h.e677 1 2 1 3 2) u6 a4 q u3
  have u8 : op 2 3 ≠ 1 := fun q => (chain op h.e677 1 2 1 3 1) u6 a4 q a3
  have u9 : op 2 3 ≠ 0 := fun q => (chain op h.e677 1 2 1 3 0) u6 a4 q u2
  exact (cellTotal (op 2 3)) u9 u8 u7 u0

theorem c1370 (op : Table) (h : Hyp op) :
    (op 1 2 = 1) → (op 0 1 = 2) → (op 1 1 ≠ 1) → (op 1 1 = 3) → (op 1 3 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) q a0
  have u4 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 2 3 1 (by decide)) a0 q
  have u5 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 1) a3 q a0 a2
  have u6 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) a3 q
  have u7 : op 3 1 ≠ 1 := fun q => (c1264 op h) a3 u4 q
  have u8 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u4 a4 u6)
  have u9 : op 3 2 ≠ 3 := fun q => (chain op h.e677 1 3 0 2 3) u8 a1 q u6
  have u10 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 0) a3 q u8 u3
  have u11 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u10 u9
    u0)
  have u12 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u7 u5 u10)
  have u13 : op 3 3 ≠ 1 := fun q => (chain op h.e677 3 0 3 1 2) u11 q a1 u2
  have u14 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) u12 q
  exact (cellTotal (op 3 3)) u14 u13 u1 u0

theorem c1371 (op : Table) (h : Hyp op) :
    (op 1 3 ≠ 1) → (op 0 1 = 2) → (op 1 1 ≠ 1) → (op 1 1 = 3) → (op 1 3 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 3 1 ≠ 1 := fun q => (c1264 op h) a3 a0 q
  have u4 : op 1 1 ≠ 2 := fun q => (cellUnique op 1 1 2 3 (by decide)) q a3
  have u5 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) a3 q
  have u6 : op 1 2 ≠ 1 := fun q => (c1370 op h) q a1 a2 a3 a4
  have u7 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q a0 a4 u5)
  have u8 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q a2 u6 a0)
  have u9 : op 1 0 ≠ 2 := fun q => (cellUnique op 1 0 1 2 (by decide)) u8 q
  have u10 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 1 3 0 1) a3 q u8 a2
  have u11 : op 1 2 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u9 u4 q
    a4)
  have u12 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 2) a3 q u11 u6
  have u13 : op 3 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u10 u3 u12 q)
  have u14 : op 3 3 ≠ 0 := fun q => (chain op h.e677 3 1 3 0 1) u13 q u8 u3
  have u15 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u14 q u1 u0)
  have u16 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u10 u2
    u14)
  have u17 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 2) q u15 a1 u2
  exact (chain op h.e677 3 3 1 0 0) u15 u7 u16 u17

end E677Finite4

namespace E677Finite4

theorem c1372 (op : Table) (h : Hyp op) :
    (op 0 1 = 2) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 1 1 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 1 3 2 (by decide)) a0 q
  have u4 : op 1 0 ≠ 3 := fun q => (rowUnique op h.inj 1 0 1 3 (by decide)) q a3
  have u5 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) a3 q
  have u6 : op 1 3 ≠ 2 := fun q => (c1369 op h) q u3 a1 a2 a3
  have u7 : op 1 2 ≠ 1 := fun q => (c1370 op h) q a0 a1 a3 u6
  have u8 : op 1 3 = 1 := Classical.byContradiction (fun q => (c1371 op h) q a0 a1 a3 u6)
  have u9 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) q u8
  have u10 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 1) a3 q u8 a1
  have u11 : op 3 3 ≠ 0 := fun q => (chain op h.e677 1 3 1 3 0) u8 a3 q u4
  have u12 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u11 q u1 u0)
  have u13 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u12
  have u14 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 2) q u12 a0 u2
  have u15 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 3 1 1 0) u12 u8 q u14
  have u16 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u15 u13 q u10)
  have u17 : op 1 2 ≠ 0 := fun q => (chain op h.e677 1 1 3 2 0) a3 u16 q u9
  have u18 : op 1 2 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 2) a3 u16 q u7
  exact (cellTotal (op 1 2)) u17 u7 u18 u5

theorem c1373 (op : Table) (h : Hyp op) :
    (op 3 1 = 2) → (op 1 0 ≠ 1) → (op 1 1 = 3) → (op 1 2 ≠ 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 1 2 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 2) a2 a0 q a3
  have u1 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) a2 q
  have u2 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q a3 u0 u1)
  exact (chain op h.e677 1 1 3 2 0) a2 a0 u2 a1

theorem c1374 (op : Table) (h : Hyp op) :
    (op 1 3 = 1) → (op 1 1 ≠ 1) → (op 1 1 = 3) → (op 1 2 ≠ 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) q a0
  have u3 : op 1 1 ≠ 2 := fun q => (cellUnique op 1 1 2 3 (by decide)) q a2
  have u4 : op 0 1 ≠ 2 := fun q => (c1372 op h) q a1 u3 a2
  have u5 : op 1 3 ≠ 0 := fun q => (cellUnique op 1 3 0 1 (by decide)) q a0
  have u6 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 1) a2 q a0 a1
  have u7 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 3 (by decide)) q a2
  have u8 : op 1 0 ≠ 3 := fun q => (rowUnique op h.inj 1 0 1 3 (by decide)) q a2
  have u9 : op 3 1 ≠ 2 := fun q => (c1373 op h) q u2 a2 a3
  have u10 : op 3 3 ≠ 0 := fun q => (chain op h.e677 1 3 1 3 0) a0 a2 q u8
  have u11 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u10 q u1 u0)
  have u12 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u11
  have u13 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u12 u9 u6)
  have u14 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 1 0 (by decide)) q u13
  have u15 : op 3 0 = 3 := Classical.byContradiction (fun q => (chain op h.e677 3 3 1 1 0) u11 a0
    u13 q)
  have u16 : op 0 1 ≠ 0 := fun q => (chain op h.e677 3 0 3 1 0) u15 u11 q u14
  have u17 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) u15 u11 q u10
  have u18 : op 0 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u16 q u4 u17)
  have u19 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) q u18
  have u20 : op 1 0 ≠ 0 := fun q => (c1258 op h) q u18 u7
  have u21 : op 1 2 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u20 u7 q
    u5)
  have u22 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u20 u2 q u8)
  exact (chain op h.e677 0 1 1 2 0) u18 u22 u21 u19

theorem c1375 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 1) → (op 1 1 ≠ 1) → (op 1 1 = 3) → (op 1 3 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 1 ≠ 2 := fun q => (cellUnique op 1 1 2 3 (by decide)) q a2
  have u4 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) a2 q
  have u5 : op 1 3 ≠ 1 := fun q => (c1374 op h) q a1 a2 a0
  have u6 : op 3 1 ≠ 1 := fun q => (c1264 op h) a2 u5 q
  have u7 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q a1 a0 u5)
  have u8 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u5 a3 u4)
  have u9 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 1 3 0 1) a2 q u7 a1
  have u10 : op 1 0 ≠ 2 := fun q => (cellUnique op 1 0 1 2 (by decide)) u7 q
  have u11 : op 1 2 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) u10 u3 q
    a3)
  have u12 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 2) a2 q u11 a0
  have u13 : op 3 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u9 u6 u12 q)
  have u14 : op 3 3 ≠ 0 := fun q => (chain op h.e677 3 1 3 0 1) u13 q u7 u6
  have u15 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u14 q u1 u0)
  have u16 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u9 u2
    u14)
  have u17 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 1 0 3) u15 u8 q u0
  exact (chain op h.e677 3 3 1 0 0) u15 u8 u16 u17

theorem c1376 (op : Table) (h : Hyp op) :
    (op 1 3 ≠ 2) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 1 1 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u3 : op 1 2 = 1 := Classical.byContradiction (fun q => (c1375 op h) q a1 a3 a0)
  have u4 : op 1 2 ≠ 2 := fun q => (cellUnique op 1 2 1 2 (by decide)) u3 q
  have u5 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) q u3
  have u6 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 2 3 1 (by decide)) u3 q
  have u7 : op 2 3 ≠ 1 := fun q => (chain op h.e677 1 2 1 3 1) u3 a3 q a2
  have u8 : op 2 3 ≠ 2 := fun q => (chain op h.e677 1 2 1 3 2) u3 a3 q u4
  have u9 : op 3 1 ≠ 1 := fun q => (c1264 op h) a3 u6 q
  have u10 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u7 u8 u1)
  have u11 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q u10
  have u12 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 1 3 3 (by decide)) a3 q
  have u13 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u6 a0 u12)
  have u14 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 1 3 2 1) a3 q u3 a1
  have u15 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 1 1 1 3) q u3 a3 u7
  have u16 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 0) a3 q u13 u5
  have u17 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u9 u14 u16)
  have u18 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) u17 q
  have u19 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u18 q u2 u0)
  have u20 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 3 1 0 3) u19 u13 q u0
  have u21 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u20 u16 q
    u0)
  have u22 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u21
  have u23 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 3 1 3) u21 u19 q u2
  have u24 : op 2 1 ≠ 2 := fun q => (chain op h.e677 3 2 3 1 2) u21 u19 q u22
  exact (cellTotal (op 2 1)) u11 u15 u24 u23

theorem c1377 (op : Table) (h : Hyp op) :
    (op 1 2 = 1) → (op 1 0 ≠ 2) → (op 1 1 ≠ 2) → (op 1 1 = 3) → (op 1 2 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 2 3 ≠ 0 := fun q => (chain op h.e677 1 2 1 3 0) a0 a3 q a1
  have u2 : op 2 3 ≠ 2 := fun q => (chain op h.e677 1 2 1 3 2) a0 a3 q a4
  have u3 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u1 q u2 u0)
  exact (chain op h.e677 1 2 1 3 1) a0 a3 u3 a2

theorem c1378 (op : Table) (h : Hyp op) :
    (op 2 3 = 2) → (op 0 1 ≠ 1) → (op 0 1 ≠ 2) → (op 0 3 ≠ 1) → (op 1 0 = 1) → (op 1 2 = 0) → (op
      1 3 = 2) → (op 3 1 ≠ 0) → (op 3 1 = 2) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 1 1 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) q a6
  have u1 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q a6
  have u2 : op 1 1 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) q a5
  have u3 : op 1 1 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) a4 q
  have u4 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 2 0 3 2) a5 q a0 u1
  have u5 : op 1 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) u2 u3 u0 q)
  have u6 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q a1 a2 u4)
  have u7 : op 0 3 = 2 := Classical.byContradiction (fun q => (c1369 op h) a6 q u3 u0 u5)
  have u8 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q u6
  have u9 : op 0 0 ≠ 2 := fun q => (rowUnique op h.inj 0 0 3 2 (by decide)) q u7
  have u10 : op 3 0 = 1 := Classical.byContradiction (fun q => (chain op h.e677 3 1 2 2 0) a8 a0
    a5 q)
  have u11 : op 0 0 ≠ 3 := fun q => (chain op h.e677 0 0 3 1 0) q u10 u6 u8
  have u12 : op 0 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u8 q u9 u11)
  exact (chain op h.e677 0 1 0 1 3) u6 u12 u5 a3

theorem c1379 (op : Table) (h : Hyp op) :
    (op 1 1 = 3) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) a0 q
  have u3 : op 0 1 ≠ 2 := fun q => (c1372 op h) q a1 a2 a0
  have u4 : op 1 3 = 2 := Classical.byContradiction (fun q => (c1376 op h) q a1 a2 a0)
  have u5 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q u4
  have u6 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) q u4
  have u7 : op 1 3 ≠ 1 := fun q => (cellUnique op 1 3 1 2 (by decide)) q u4
  have u8 : op 0 3 = 2 := Classical.byContradiction (fun q => (c1369 op h) u4 q a1 a2 a0)
  have u9 : op 1 2 ≠ 1 := fun q => (c1377 op h) q u5 a2 a0 u6
  have u10 : op 1 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) q u9 u6 u2)
  have u11 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q a1 u9
    u7)
  have u12 : op 3 1 ≠ 1 := fun q => (c1264 op h) a0 u7 q
  have u13 : op 0 3 ≠ 0 := fun q => (cellUnique op 0 3 0 2 (by decide)) q u8
  have u14 : op 0 3 ≠ 1 := fun q => (cellUnique op 0 3 1 2 (by decide)) q u8
  have u15 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 2 3 (by decide)) u8 q
  have u16 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 1 3 3 2) a0 q u4 u9
  have u17 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 1 3) q u11 a0 u14
  have u18 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 1 3 0 1) a0 q u11 a1
  have u19 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u18 u12 q u16)
  have u20 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 1 2 0 1) u19 q u11 u12
  have u21 : op 2 3 ≠ 2 := fun q => (c1378 op h) q u17 u3 u14 u11 u10 u4 u18 u19
  have u22 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u20 q u21 u0)
  have u23 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 2 0 3 1) u10 q u22 a2
  have u24 : op 3 3 = 1 := Classical.byContradiction (fun q => (chain op h.e677 3 1 2 1 3) u19 u22
    a0 q)
  have u25 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 1 (by decide)) q u24
  have u26 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u18 u1
    u25)
  have u27 : op 0 0 ≠ 3 := fun q => (c1254 op h) q u13 u26
  have u28 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 0 2 3) u26 u8 q u25
  exact (rowTotal op h.surj 0 3) u27 u23 u28 u15

theorem c1380 (op : Table) (h : Hyp op) :
    (op 1 3 = 2) → (op 1 1 = 0) → (op 1 1 ≠ 1) → (op 1 2 ≠ 1) → (op 1 2 = 3) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q a0
  have u1 : op 1 0 ≠ 0 := fun q => (rowUnique op h.inj 1 0 1 0 (by decide)) q a1
  have u2 : op 1 2 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) a1 q
  have u3 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 1 3 0 (by decide)) a1 q
  have u4 : op 1 0 ≠ 3 := fun q => (rowUnique op h.inj 1 0 2 3 (by decide)) q a4
  have u5 : op 1 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u1 q u0 u4)
  have u6 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) u5 q
  have u7 : op 0 0 ≠ 3 := fun q => (chain op h.e677 1 0 1 0 3) u5 a1 q u3
  have u8 : op 0 0 ≠ 2 := fun q => (chain op h.e677 1 0 1 0 2) u5 a1 q u2
  have u9 : op 0 1 ≠ 0 := fun q => (chain op h.e677 1 1 0 0 1) a1 q u5 a2
  have u10 : op 0 0 ≠ 0 := fun q => (chain op h.e677 1 0 1 0 0) u5 a1 q u1
  have u11 : op 0 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u10 q u8 u7)
  have u12 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) u11 q
  have u13 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 2) a1 q a0 a3
  have u14 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u9 u12 q u13)
  exact (chain op h.e677 1 1 0 2 3) a1 u14 a4 u6

theorem c1381 (op : Table) (h : Hyp op) :
    (op 0 0 = 1) → (op 0 1 ≠ 0) → (op 0 1 = 2) → (op 1 0 = 2) → (op 1 2 = 3) → (op 2 0 ≠ 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q a0
  have u2 : op 0 0 ≠ 3 := fun q => (cellUnique op 0 0 1 3 (by decide)) a0 q
  have u3 : op 1 0 ≠ 0 := fun q => (c1252 op h) a0 a1 q
  have u4 : op 0 2 ≠ 0 := fun q => (chain op h.e677 0 0 1 2 0) a0 a3 q u1
  have u5 : op 1 2 ≠ 0 := fun q => (cellUnique op 1 2 0 3 (by decide)) q a4
  have u6 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 2 3 3 (by decide)) a4 q
  have u7 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) a3 q
  have u8 : op 0 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) u1 a1 u4 q)
  have u9 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 0 3 (by decide)) u8 q
  have u10 : op 3 1 ≠ 0 := fun q => (chain op h.e677 0 3 0 1 0) u8 a0 q u2
  have u11 : op 3 1 ≠ 3 := fun q => (chain op h.e677 0 3 0 1 3) u8 a0 q u9
  have u12 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 0 1) q u8 a0 u10
  have u13 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u12 u10 u0
    q)
  have u14 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u13 q
  have u15 : op 3 0 ≠ 1 := fun q => (chain op h.e677 3 3 0 0 1) u13 u8 q u11
  have u16 : op 0 2 ≠ 1 := fun q => (rowUnique op h.inj 0 0 2 1 (by decide)) a0 q
  have u17 : op 0 2 ≠ 2 := fun q => (chain op h.e677 0 0 1 2 2) a0 a3 q u4
  have u18 : op 0 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u4 u16 u17 q)
  have u19 : op 0 1 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) q u18
  have u20 : op 3 1 ≠ 1 := fun q => (chain op h.e677 0 3 0 1 1) u8 a0 q u19
  have u21 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u10 u20 q u11)
  have u22 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u15 u20 q
    u14)
  have u23 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) q u21
  have u24 : op 3 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u12 u15 u23 q)
  have u25 : op 1 1 ≠ 3 := fun q => (rowUnique op h.inj 1 1 2 3 (by decide)) q a4
  have u26 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 2 1) q a2 u22 u25
  have u27 : op 1 1 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u3 q u5
    u26)
  have u28 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u26 q u7 u6)
  exact (chain op h.e677 1 3 1 0 3) u28 u27 u24 u6

theorem c1382 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 2) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → (op 1 2 ≠ 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 1 ≠ 3 := fun q => (c1379 op h) q a1 a2
  have u3 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q a1 a2 u2)
  have u4 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 1 3 0 (by decide)) u3 q
  have u5 : op 1 2 ≠ 0 := fun q => (rowUnique op h.inj 1 1 2 0 (by decide)) u3 q
  have u6 : op 1 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 2)) u5 a3 a0 q)
  have u7 : op 1 0 ≠ 3 := fun q => (rowUnique op h.inj 1 0 2 3 (by decide)) q u6
  have u8 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 2 3 3 (by decide)) u6 q
  have u9 : op 1 3 ≠ 2 := fun q => (c1380 op h) q u3 a1 a3 u6
  have u10 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u4 q u9 u8)
  have u11 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 1) u3 q u10 a1
  have u12 : op 3 0 ≠ 1 := fun q => (chain op h.e677 1 3 1 0 1) u10 u3 q u2
  have u13 : op 3 0 ≠ 3 := fun q => (chain op h.e677 1 3 1 0 3) u10 u3 q u8
  have u14 : op 3 0 ≠ 0 := fun q => (chain op h.e677 1 3 1 0 0) u10 u3 q u7
  have u15 : op 3 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u14 u12 q u13)
  have u16 : op 1 0 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 2) q a2 a0
    u9)
  have u17 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 3 1 (by decide)) q u10
  have u18 : op 0 1 ≠ 1 := fun q => (c1259 op h) u3 q u17
  have u19 : op 0 1 ≠ 0 := fun q => (chain op h.e677 1 1 0 0 2) u3 q u16 a3
  have u20 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u19 u18 q u11)
  have u21 : op 2 1 ≠ 1 := fun q => (chain op h.e677 1 0 2 1 2) u16 q u20 u5
  have u22 : op 2 3 ≠ 1 := fun q => (chain op h.e677 3 0 2 1 2) u15 q u20 u1
  have u23 : op 2 0 ≠ 3 := fun q => (chain op h.e677 0 1 2 3 1) u20 q u10 u18
  have u24 : op 0 0 ≠ 1 := fun q => (c1381 op h) q u19 u20 u16 u6 u23
  have u25 : op 2 0 ≠ 1 := fun q => (chain op h.e677 0 1 2 1 0) u20 q u3 u24
  have u26 : op 2 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 1) u25 u21 q
    u22)
  have u27 : op 2 2 ≠ 0 := fun q => (cellUnique op 2 2 0 1 (by decide)) q u26
  have u28 : op 2 2 ≠ 2 := fun q => (cellUnique op 2 2 1 2 (by decide)) u26 q
  have u29 : op 2 3 ≠ 2 := fun q => (chain op h.e677 2 2 1 3 2) u26 u6 q u28
  have u30 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u22 u29 u0)
  have u31 : op 2 0 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) q u30
  have u32 : op 2 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u31 u25 q u23)
  exact (chain op h.e677 2 0 2 1 2) u32 u26 u20 u27

theorem c1383 (op : Table) (h : Hyp op) :
    (op 1 3 = 1) → (op 0 1 ≠ 2) → (op 1 1 = 0) → (op 1 1 ≠ 1) → (op 1 1 ≠ 3) → (op 1 2 ≠ 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 1 3 (by decide)) a0 q
  have u3 : op 1 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) q a4 a5 u2)
  have u4 : op 1 0 ≠ 1 := fun q => (cellUnique op 1 0 1 3 (by decide)) q u3
  have u5 : op 0 1 ≠ 1 := fun q => (c1259 op h) a2 q u4
  have u6 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 1) a2 q a0 a3
  have u7 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u5 a1 u6)
  have u8 : op 0 3 ≠ 0 := fun q => (rowUnique op h.inj 0 1 3 0 (by decide)) u7 q
  have u9 : op 3 0 ≠ 1 := fun q => (chain op h.e677 1 3 1 0 1) a0 a2 q a4
  have u10 : op 3 0 ≠ 2 := fun q => (chain op h.e677 1 3 1 0 2) a0 a2 q a5
  have u11 : op 3 0 ≠ 3 := fun q => (chain op h.e677 1 3 1 0 3) a0 a2 q u2
  have u12 : op 3 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) q u9 u10 u11)
  have u13 : op 0 0 ≠ 3 := fun q => (c1254 op h) q u8 u12
  have u14 : op 0 3 ≠ 3 := fun q => (c1257 op h) q u13 u12
  have u15 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 0 3 0 (by decide)) u12 q
  have u16 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u15 q u1 u0)
  have u17 : op 0 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 1) q u3 u16 u6
  have u18 : op 0 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u8 u17 q u14)
  have u19 : op 0 2 ≠ 3 := fun q => (chain op h.e677 3 0 0 2 3) u12 u18 q u15
  exact (rowTotal op h.surj 0 3) u13 u6 u19 u14

theorem c1384 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 1) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 1 1 ≠ 3 := fun q => (c1379 op h) q a1 a2
  have u1 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q a1 a2 u0)
  have u2 : op 1 0 ≠ 0 := fun q => (rowUnique op h.inj 1 0 1 0 (by decide)) q u1
  have u3 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 1 3 0 (by decide)) u1 q
  have u4 : op 1 2 = 2 := Classical.byContradiction (fun q => (c1382 op h) q a1 a2 a0)
  have u5 : op 1 2 ≠ 0 := fun q => (cellUnique op 1 2 0 2 (by decide)) q u4
  have u6 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 2 3 (by decide)) u4 q
  have u7 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 2 3 2 (by decide)) u4 q
  have u8 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 1 0 2 2) u1 q u4 a0
  have u9 : op 1 3 ≠ 1 := fun q => (c1383 op h) q u8 u1 a1 u0 u6
  have u10 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q a1 a0
    u9)
  have u11 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u3 u9 u7 q)
  have u12 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 3) u1 q u11 u9
  have u13 : op 0 0 ≠ 3 := fun q => (chain op h.e677 1 0 1 0 3) u10 u1 q u3
  have u14 : op 0 0 ≠ 2 := fun q => (chain op h.e677 1 0 1 0 2) u10 u1 q u5
  have u15 : op 0 1 ≠ 0 := fun q => (chain op h.e677 1 1 0 0 1) u1 q u10 a1
  have u16 : op 0 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u15 q u8 u12)
  have u17 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) q u16
  have u18 : op 0 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) q u17 u14 u13)
  exact (chain op h.e677 1 0 1 0 0) u10 u1 u18 u2

theorem c1385 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 3) → (op 0 1 ≠ 2) → (op 1 1 = 0) → (op 1 1 ≠ 3) → (op 1 2 = 1) → (op 2 0 ≠ 1) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 0 ≠ 0 := fun q => (rowUnique op h.inj 1 0 1 0 (by decide)) q a2
  have u3 : op 1 2 ≠ 2 := fun q => (cellUnique op 1 2 1 2 (by decide)) a4 q
  have u4 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 1 3 (by decide)) a4 q
  have u5 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) q a4
  have u6 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 2 3 1 (by decide)) a4 q
  have u7 : op 2 0 ≠ 2 := fun q => (chain op h.e677 1 2 1 0 2) a4 a2 q u3
  have u8 : op 0 1 ≠ 1 := fun q => (c1259 op h) a2 q u5
  have u9 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u8 a1 a0)
  have u10 : op 0 2 ≠ 0 := fun q => (rowUnique op h.inj 0 1 2 0 (by decide)) u9 q
  have u11 : op 1 0 ≠ 3 := fun q => (chain op h.e677 1 1 0 0 3) a2 u9 q u6
  have u12 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u2 u5 q u11)
  have u13 : op 1 3 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u11 a3 u4
    q)
  have u14 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) u12 q
  have u15 : op 3 1 ≠ 1 := fun q => (c1266 op h) u13 a3 q
  have u16 : op 0 0 ≠ 2 := fun q => (chain op h.e677 0 1 0 2 1) u9 q a4 u8
  have u17 : op 2 0 ≠ 3 := fun q => (chain op h.e677 1 2 1 0 3) a4 a2 q u14
  have u18 : op 2 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) q a5 u7 u17)
  have u19 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 0 2 0 (by decide)) u18 q
  have u20 : op 0 2 ≠ 2 := fun q => (c1267 op h) u18 q u19
  have u21 : op 0 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 2) u16 a1 u20
    q)
  have u22 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 2 1) q u21 a4 u15
  have u23 : op 0 2 ≠ 3 := fun q => (chain op h.e677 2 0 0 3 2) u18 q u21 u19
  have u24 : op 0 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) u10 q u20 u23)
  have u25 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 2 1) q u21 u24 u22
  have u26 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u25 u22 u1
    q)
  have u27 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 0 2 3) u26 u21 q u0
  have u28 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) u13 q u26 u11
  have u29 : op 3 2 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) u26 u21 q u27
  have u30 : op 3 2 ≠ 1 := fun q => (chain op h.e677 3 3 0 2 1) u26 u21 q u28
  exact (cellTotal (op 3 2)) u1 u30 u29 u27

theorem c1386 (op : Table) (h : Hyp op) :
    (op 0 3 = 2) → (op 0 0 ≠ 3) → (op 1 2 = 1) → (op 2 0 = 3) → (op 3 0 ≠ 0) → (op 3 1 ≠ 1) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 1 3 (by decide)) a2 q
  have u3 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 2 1) q a0 a2 a5
  have u4 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) a4 u3 u1 q)
  have u5 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u4 q
  have u6 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 0 2 3) u4 a0 q u0
  have u7 : op 3 2 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) u4 a0 q u6
  have u8 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u1 q u7 u6)
  have u9 : op 3 1 = 3 := Classical.byContradiction (fun q => (chain op h.e677 3 3 0 2 1) u4 a0 u8
    q)
  have u10 : op 1 0 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) u9 u4 q u5
  have u11 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) q u9 u4 u10
  have u12 : op 1 1 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u10 q u2
    u11)
  have u13 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 3 (by decide)) q u12
  have u14 : op 1 1 ≠ 2 := fun q => (cellUnique op 1 1 2 3 (by decide)) q u12
  exact (c1379 op h) u12 u13 u14

theorem c1387 (op : Table) (h : Hyp op) :
    (op 0 3 ≠ 1) → (op 0 0 ≠ 2) → (op 0 1 ≠ 1) → (op 0 1 ≠ 2) → (op 0 1 = 3) → (op 1 0 = 3) → (op
      1 2 = 1) → (op 2 0 = 3) → (op 3 1 ≠ 1) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 3 0 ≠ 0 := fun q => (chain op h.e677 0 1 3 0 3) a4 q a5 a0
  have u1 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a4
  have u2 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a4 q
  have u3 : op 0 3 ≠ 2 := fun q => (c1386 op h) q u1 a6 a7 u0 a8
  have u4 : op 0 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) q a0 u3 u2)
  have u5 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 3 0 (by decide)) q u4
  have u6 : op 0 0 ≠ 1 := fun q => (chain op h.e677 0 0 1 3 0) q a5 u4 u5
  exact (cellTotal (op 0 0)) u5 u6 a1 u1

theorem c1388 (op : Table) (h : Hyp op) :
    (op 0 0 ≠ 2) → (op 0 1 ≠ 1) → (op 0 1 ≠ 2) → (op 0 1 = 3) → (op 1 0 ≠ 0) → (op 1 0 = 3) → (op
      1 2 = 1) → (op 2 0 = 3) → (op 3 1 ≠ 1) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a3
  have u2 : op 0 3 = 1 := Classical.byContradiction (fun q => (c1387 op h) q a0 a1 a2 a3 a5 a6 a7
    a8)
  have u3 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) q u2
  have u4 : op 3 3 ≠ 0 := fun q => (chain op h.e677 0 3 1 3 0) u2 a5 q u1
  have u5 : op 0 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) q u3 a0 u1)
  have u6 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 1 3) q u2 a3 u4
  have u7 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 0) a5 q u5 a4
  exact (rowTotal op h.surj 3 0) u6 u7 u0 u4

theorem c1389 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 3) → (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 1 2 = 1 := Classical.byContradiction (fun q => (c1384 op h) q a1 a2)
  have u1 : op 1 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 1)) q a1 a2 a0)
  have u2 : op 1 2 ≠ 2 := fun q => (cellUnique op 1 2 1 2 (by decide)) u0 q
  have u3 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 1 3 (by decide)) u0 q
  have u4 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 2 1 (by decide)) q u0
  have u5 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 2 3 1 (by decide)) u0 q
  have u6 : op 1 0 ≠ 0 := fun q => (rowUnique op h.inj 1 0 1 0 (by decide)) q u1
  have u7 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 1 3 0 (by decide)) u1 q
  have u8 : op 2 0 ≠ 2 := fun q => (chain op h.e677 1 2 1 0 2) u0 u1 q u2
  have u9 : op 2 0 ≠ 1 := fun q => (chain op h.e677 1 2 1 0 1) u0 u1 q a2
  have u10 : op 0 1 ≠ 1 := fun q => (c1259 op h) u1 q u4
  have u11 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 1 0 2 1) u1 q u0 a1
  have u12 : op 0 1 = 3 := Classical.byContradiction (fun q => (c1385 op h) q u11 u1 a0 u0 u9)
  have u13 : op 0 1 ≠ 0 := fun q => (cellUnique op 0 1 0 3 (by decide)) q u12
  have u14 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) u12 q
  have u15 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 1 0 3 3) u1 u12 q u5
  have u16 : op 1 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) q a0 u3
    u15)
  have u17 : op 1 0 ≠ 2 := fun q => (cellUnique op 1 0 2 3 (by decide)) q u16
  have u18 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 0 3 1 3) u16 q u12 u7
  have u19 : op 2 0 ≠ 0 := fun q => (chain op h.e677 1 2 1 0 0) u0 u1 q u17
  have u20 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u19 u9 u8 q)
  have u21 : op 0 0 = 2 := Classical.byContradiction (fun q => (c1388 op h) q u10 u11 u12 u6 u16
    u0 u20 u18)
  have u22 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 2 (by decide)) q u21
  have u23 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 0 3 2 (by decide)) u21 q
  have u24 : op 0 3 ≠ 1 := fun q => (chain op h.e677 0 0 2 3 1) u21 u20 q u13
  have u25 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 0 2 3 0) u21 u20 q u22
  exact (cellTotal (op 0 3)) u25 u24 u23 u14

theorem c1390 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 1 1 ≠ 3 := fun q => (c1379 op h) q a0 a1
  exact (c1389 op h) u0 a0 a1

theorem c1391 (op : Table) (h : Hyp op) :
    (op 1 2 = 0) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 2) → (op 2 0 ≠ 1) → (op 2 0 = 3) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 1 0 ≠ 2 := fun q => (cellUnique op 1 0 2 3 (by decide)) q a2
  have u2 : op 1 2 ≠ 2 := fun q => (cellUnique op 1 2 0 2 (by decide)) a0 q
  have u3 : op 2 3 ≠ 2 := fun q => (chain op h.e677 1 2 0 3 2) a0 a1 q u2
  have u4 : op 2 3 ≠ 0 := fun q => (chain op h.e677 1 2 0 3 0) a0 a1 q u1
  have u5 : op 2 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u4 q u3 u0)
  exact (chain op h.e677 1 2 0 3 1) a0 a1 u5 a3

theorem c1392 (op : Table) (h : Hyp op) :
    (op 2 0 = 3) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 2) → (op 2 0 ≠ 1) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u3 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a1
  have u4 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 3 (by decide)) q a2
  have u5 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u2
  have u6 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u2 q
  have u7 : op 3 0 ≠ 1 := fun q => (chain op h.e677 0 1 3 1 1) a1 q u2 u3
  have u8 : op 1 2 ≠ 0 := fun q => (c1391 op h) q a1 a2 a3 a4 a0
  have u9 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u4 u5 u8 q)
  have u10 : op 3 3 ≠ 1 := fun q => (chain op h.e677 1 3 0 3 1) u9 a1 q u6
  have u11 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 1 1 0 3) q u9 a2 u10
  have u12 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u10 u1 u0)
  have u13 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u7 u11 q
    u10)
  have u14 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q u12
  have u15 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u12 a2 u10
  have u16 : op 2 3 = 0 := Classical.byContradiction (fun q => (chain op h.e677 2 0 3 1 3) a0 u13
    a1 q)
  have u17 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u14 u11 q u15)
  exact (chain op h.e677 3 1 2 0 3) u17 u16 a2 u10

theorem c1393 (op : Table) (h : Hyp op) :
    (op 2 0 = 0) → (op 0 1 = 3) → False := by
  intro a0 a1
  have u0 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 0 1 0 (by decide)) a0 q
  have u1 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 0 2 0 (by decide)) a0 q
  have u2 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a1
  have u3 : op 0 2 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) a1 q
  have u4 : op 2 3 ≠ 0 := fun q => (rowUnique op h.inj 2 0 3 0 (by decide)) a0 q
  have u5 : op 0 2 ≠ 2 := fun q => (c1267 op h) a0 q u1
  have u6 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 0 0 1 3) a0 q a1 u4
  have u7 : op 0 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 2)) q u6 u5 u3)
  have u8 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 2 0 (by decide)) q u7
  have u9 : op 0 0 ≠ 2 := fun q => (chain op h.e677 2 0 0 0 2) a0 u7 q u1
  have u10 : op 0 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u8 q u9 u2)
  exact (chain op h.e677 2 0 0 0 1) a0 u7 u10 u0

theorem c1394 (op : Table) (h : Hyp op) :
    (op 0 0 ≠ 0) → (op 0 0 ≠ 2) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 0) → (op 2 0 = 2) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a2
  have u3 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a2 q
  have u4 : op 0 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) a0 q a1 u2)
  have u5 : op 0 3 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) u4 q
  have u6 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 1) a3 q u4 a4
  have u7 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 0 1 3 0) u4 a3 q a0
  have u8 : op 3 0 ≠ 0 := fun q => (chain op h.e677 0 1 3 0 3) a2 q a3 u5
  have u9 : op 0 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u7 u5 q u3)
  have u10 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u8 u6 u1
    q)
  have u11 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 0 2 3) u10 u9 q u0
  have u12 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u10 q
  have u13 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u10 a3 u12
  have u14 : op 3 2 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) u10 u9 q u11
  have u15 : op 3 2 ≠ 1 := fun q => (chain op h.e677 3 3 0 2 1) u10 u9 q u13
  exact (cellTotal (op 3 2)) u1 u15 u14 u11

theorem c1395 (op : Table) (h : Hyp op) :
    (op 3 3 ≠ 1) → (op 0 1 = 3) → (op 0 3 ≠ 0) → (op 1 0 = 3) → (op 2 0 = 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q a0 u1 u0)
  have u4 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a1
  have u5 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a1 q
  have u6 : op 0 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 0) q a3 u3 u4
  have u7 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u3 a3 a0
  have u8 : op 0 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) a2 u6 q u5)
  have u9 : op 3 2 ≠ 1 := fun q => (chain op h.e677 3 3 0 2 1) u3 u8 q u7
  have u10 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 0 2 3) u3 u8 q u0
  have u11 : op 3 2 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) u3 u8 q u10
  exact (cellTotal (op 3 2)) u2 u9 u11 u10

theorem c1396 (op : Table) (h : Hyp op) :
    (op 0 0 = 0) → (op 0 1 = 3) → (op 1 0 = 3) → (op 2 0 = 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 3 ≠ 0 := fun q => (rowUnique op h.inj 0 0 3 0 (by decide)) a0 q
  have u2 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 3 (by decide)) q a2
  have u3 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 0) a2 q a0 u2
  have u4 : op 3 3 = 1 := Classical.byContradiction (fun q => (c1395 op h) q a1 u1 a2 a3)
  have u5 : op 3 3 ≠ 0 := fun q => (cellUnique op 3 3 0 1 (by decide)) q u4
  have u6 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u3 u0 u5)
  have u7 : op 0 3 = 1 := Classical.byContradiction (fun q => (chain op h.e677 0 1 3 0 3) a1 u6 a2
    q)
  exact (chain op h.e677 3 0 0 1 3) u6 u7 a1 u5

theorem c1397 (op : Table) (h : Hyp op) :
    (op 2 0 = 2) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 0) → False := by
  intro a0 a1 a2 a3
  have u0 : op 0 1 ≠ 0 := fun q => (cellUnique op 0 1 0 3 (by decide)) q a1
  have u1 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a1
  have u2 : op 0 0 ≠ 0 := fun q => (c1396 op h) q a1 a2 a0
  have u3 : op 0 0 = 2 := Classical.byContradiction (fun q => (c1394 op h) u2 q a1 a2 a3 a0)
  have u4 : op 0 0 ≠ 1 := fun q => (cellUnique op 0 0 1 2 (by decide)) q u3
  have u5 : op 0 2 ≠ 1 := fun q => (chain op h.e677 0 0 2 2 1) u3 a0 q u0
  have u6 : op 0 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u4 u1 u5 q)
  have u7 : op 0 3 ≠ 0 := fun q => (cellUnique op 0 3 0 1 (by decide)) q u6
  have u8 : op 0 2 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) u2 u0 q u7)
  exact (chain op h.e677 0 0 2 2 0) u3 a0 u8 u2

theorem c1398 (op : Table) (h : Hyp op) :
    (op 2 0 ≠ 1) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 0 ≠ 0 := fun q => (c1393 op h) q a1
  have u1 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u2 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u1
  have u3 : op 2 0 ≠ 2 := fun q => (c1397 op h) q a1 a2 u2
  have u4 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u0 a0 u3 q)
  exact (c1392 op h) u4 a1 a2 a3 a0

theorem c1399 (op : Table) (h : Hyp op) :
    (op 0 0 = 2) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 0) → (op 2 0 = 1) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a1
  have u4 : op 0 2 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) a1 q
  have u5 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a1 q
  have u6 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 3 (by decide)) q a2
  have u7 : op 0 0 ≠ 1 := fun q => (cellUnique op 0 0 1 2 (by decide)) q a0
  have u8 : op 0 3 = 0 := Classical.byContradiction (fun q => (chain op h.e677 0 0 2 1 3) a0 a4 a1
    q)
  have u9 : op 0 3 ≠ 1 := fun q => (cellUnique op 0 3 0 1 (by decide)) u8 q
  have u10 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 0 3 3 0) a2 q u8 u6
  have u11 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u7 u3 q
    u9)
  have u12 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 0 3 2 1) a2 q u11 a3
  have u13 : op 3 2 ≠ 3 := fun q => (chain op h.e677 0 3 0 2 3) u8 a0 q u5
  have u14 : op 3 2 ≠ 2 := fun q => (chain op h.e677 0 3 0 2 2) u8 a0 q u4
  have u15 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u2 q u14 u13)
  have u16 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u15
  have u17 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u15 q
  have u18 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u16 u12 u10)
  have u19 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u17 u1 u0)
  exact (rowUnique op h.inj 3 1 3 0 (by decide)) u18 u19

theorem c1400 (op : Table) (h : Hyp op) :
    (op 0 0 ≠ 0) → (op 0 1 = 3) → (op 1 0 = 3) → (op 1 1 ≠ 0) → (op 2 0 = 1) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a1
  have u3 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a1 q
  have u4 : op 0 0 ≠ 2 := fun q => (c1399 op h) q a1 a2 a3 a4
  have u5 : op 0 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) a0 q u4 u2)
  have u6 : op 0 3 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) u5 q
  have u7 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 0 1 3 0) u5 a2 q a0
  have u8 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 1) a2 q u5 a3
  have u9 : op 0 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u7 u6 q u3)
  have u10 : op 3 0 ≠ 0 := fun q => (chain op h.e677 0 1 3 0 3) a1 q a2 u6
  have u11 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u10 u8 u1
    q)
  have u12 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u11 q
  have u13 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u11 a2 u12
  have u14 : op 3 2 ≠ 3 := fun q => (chain op h.e677 3 3 0 2 3) u11 u9 q u0
  have u15 : op 3 2 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) u11 u9 q u14
  have u16 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u1 q u15 u14)
  exact (chain op h.e677 3 3 0 2 1) u11 u9 u16 u13

theorem c1401 (op : Table) (h : Hyp op) :
    (op 1 0 = 3) → (op 0 1 = 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a1
  have u3 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a1
  have u4 : op 2 0 ≠ 0 := fun q => (c1393 op h) q a1
  have u5 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a2)
  have u6 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u5
  have u7 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u5 q
  have u8 : op 1 0 ≠ 0 := fun q => (cellUnique op 1 0 0 3 (by decide)) q a0
  have u9 : op 2 0 = 1 := Classical.byContradiction (fun q => (c1398 op h) q a1 a0 a2)
  have u10 : op 0 0 = 0 := Classical.byContradiction (fun q => (c1400 op h) q a1 a0 u6 u9)
  have u11 : op 0 0 ≠ 1 := fun q => (cellUnique op 0 0 0 1 (by decide)) u10 q
  have u12 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 0) a0 q u10 u8
  have u13 : op 1 2 ≠ 0 := fun q => (chain op h.e677 2 0 1 0 0) u9 q u10 u4
  have u14 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u8 u6 u13
    q)
  have u15 : op 3 3 ≠ 1 := fun q => (chain op h.e677 1 3 0 3 1) u14 a1 q u7
  have u16 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 1 1 0 3) q u14 a0 u15
  have u17 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u15 u1 u0)
  have u18 : op 0 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 0) q a0 u17 u3
  have u19 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u17 a0 u15
  have u20 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u11 u2 q
    u18)
  have u21 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u12 u16 q u19)
  exact (chain op h.e677 1 0 3 2 1) a0 u21 u20 u6

theorem c1402 (op : Table) (h : Hyp op) :
    (op 0 2 = 1) → (op 0 1 = 3) → (op 0 3 ≠ 1) → (op 1 0 ≠ 3) → (op 1 1 = 1) → (op 2 0 = 1) →
      False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 0 2 ≠ 2 := fun q => (cellUnique op 0 2 1 2 (by decide)) a0 q
  have u3 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) q a0
  have u4 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a4
  have u5 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) a4 q
  have u6 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q a4
  have u7 : op 0 1 ≠ 2 := fun q => (chain op h.e677 0 1 2 1 1) q a5 a4 u3
  have u8 : op 1 0 ≠ 0 := fun q => (chain op h.e677 0 2 1 0 1) a0 q a5 u7
  have u9 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u8 u6 q a3)
  have u10 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) u9 q
  have u11 : op 2 1 ≠ 2 := fun q => (chain op h.e677 1 0 2 2 1) u9 q a0 u4
  have u12 : op 2 0 ≠ 2 := fun q => (cellUnique op 2 0 1 2 (by decide)) a5 q
  have u13 : op 2 2 ≠ 2 := fun q => (chain op h.e677 0 2 1 2 2) a0 u9 q u2
  have u14 : op 2 3 = 2 := Classical.byContradiction (fun q => (rowTotal op h.surj 2 2) u12 u11
    u13 q)
  have u15 : op 1 2 ≠ 0 := fun q => (chain op h.e677 1 2 0 3 2) q a1 u14 u10
  have u16 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u8 u4 u15
    q)
  have u17 : op 3 3 ≠ 1 := fun q => (chain op h.e677 1 3 0 3 1) u16 a1 q u5
  have u18 : op 3 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 0) u16 a1 q a3
  exact (cellTotal (op 3 3)) u18 u17 u1 u0

theorem c1403 (op : Table) (h : Hyp op) :
    (op 0 3 ≠ 1) → (op 0 1 = 3) → (op 1 0 ≠ 3) → (op 1 1 = 1) → (op 2 0 = 1) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) a3 q
  have u2 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q a3
  have u3 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a3 q
  have u4 : op 0 1 ≠ 0 := fun q => (cellUnique op 0 1 0 3 (by decide)) q a1
  have u5 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a1
  have u6 : op 0 0 ≠ 3 := fun q => (rowUnique op h.inj 0 0 1 3 (by decide)) q a1
  have u7 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 1 3 3 (by decide)) a1 q
  have u8 : op 3 0 ≠ 1 := fun q => (chain op h.e677 0 1 3 1 1) a1 q a3 u5
  have u9 : op 0 2 ≠ 1 := fun q => (c1402 op h) q a1 a0 a2 a3 a4
  have u10 : op 0 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) q u5 u9
    a0)
  have u11 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q u10
  have u12 : op 1 0 ≠ 0 := fun q => (c1252 op h) u10 u4 q
  have u13 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u12 u2 q a2)
  have u14 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) u13 q
  have u15 : op 0 2 ≠ 0 := fun q => (chain op h.e677 0 0 1 2 0) u10 u13 q u11
  have u16 : op 0 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) u11 u4 u15
    q)
  have u17 : op 3 1 ≠ 3 := fun q => (chain op h.e677 0 3 0 1 3) u16 u10 q u7
  have u18 : op 3 1 ≠ 0 := fun q => (chain op h.e677 0 3 0 1 0) u16 u10 q u6
  have u19 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 0 1) q u16 u10 u18
  have u20 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u19 u18 u0
    q)
  have u21 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u20 q
  have u22 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 0) q a1 u20 a2
  have u23 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u22 u3 u14 q)
  have u24 : op 3 1 ≠ 1 := fun q => (c1266 op h) u23 u1 q
  have u25 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u18 u24 q u17)
  have u26 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u8 u24 q
    u21)
  exact (chain op h.e677 1 3 3 2 1) u23 u25 u26 u1

theorem c1404 (op : Table) (h : Hyp op) :
    (op 2 0 = 1) → (op 0 1 = 3) → (op 1 0 ≠ 3) → (op 1 1 = 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a3
  have u4 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q a3
  have u5 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a3 q
  have u6 : op 0 2 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) a1 q
  have u7 : op 0 3 = 1 := Classical.byContradiction (fun q => (c1403 op h) q a1 a2 a3 a0)
  have u8 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 1 3 (by decide)) u7 q
  have u9 : op 1 0 ≠ 0 := fun q => (chain op h.e677 1 0 0 3 1) q a1 u7 u3
  have u10 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u9 u4 q a2)
  have u11 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) u10 q
  have u12 : op 3 2 ≠ 3 := fun q => (chain op h.e677 0 3 1 2 3) u7 u10 q u8
  have u13 : op 3 2 ≠ 2 := fun q => (chain op h.e677 0 3 1 2 2) u7 u10 q u6
  have u14 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u2 q u13 u12)
  have u15 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u14
  have u16 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u14 q
  have u17 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 1 1) q u7 a3 u15
  have u18 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u16 u1 u0)
  have u19 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 0) q a1 u18 a2
  have u20 : op 3 1 ≠ 2 := fun q => (chain op h.e677 3 3 0 1 2) u18 u7 q u12
  have u21 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u19 u5 u11 q)
  have u22 : op 3 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u17 u15 u20 q)
  exact (chain op h.e677 1 3 3 3 0) u21 u22 u18 a2

theorem c1405 (op : Table) (h : Hyp op) :
    (op 0 3 = 1) → (op 0 1 = 3) → (op 1 0 ≠ 3) → (op 1 1 = 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 1 3 (by decide)) a0 q
  have u4 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q a3
  have u5 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q a3
  have u6 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a3 q
  have u7 : op 1 0 ≠ 0 := fun q => (chain op h.e677 1 0 0 3 1) q a1 a0 u4
  have u8 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u7 u5 q a2)
  have u9 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) u8 q
  have u10 : op 0 2 ≠ 3 := fun q => (rowUnique op h.inj 0 1 2 3 (by decide)) a1 q
  have u11 : op 3 2 ≠ 3 := fun q => (chain op h.e677 0 3 1 2 3) a0 u8 q u3
  have u12 : op 3 2 ≠ 2 := fun q => (chain op h.e677 0 3 1 2 2) a0 u8 q u10
  have u13 : op 3 2 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u2 q u12 u11)
  have u14 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u13
  have u15 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u13 q
  have u16 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 1 1) q a0 a3 u14
  have u17 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u15 u1 u0)
  have u18 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 0) q a1 u17 a2
  have u19 : op 3 1 ≠ 2 := fun q => (chain op h.e677 3 3 0 1 2) u17 a0 q u11
  have u20 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u18 u6 u9 q)
  have u21 : op 3 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u16 u14 u19 q)
  exact (chain op h.e677 1 3 3 3 0) u20 u21 u17 a2

theorem c1406 (op : Table) (h : Hyp op) :
    (op 3 3 = 0) → (op 0 1 = 3) → (op 1 0 ≠ 3) → (op 1 1 = 1) → (op 1 3 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a0 q
  have u3 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a0
  have u4 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 0) q a1 a0 a2
  have u5 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) a3 q
  have u6 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a3 q
  have u7 : op 0 3 ≠ 1 := fun q => (c1405 op h) q a1 a2 a3
  have u8 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u4 u6 a4 q)
  have u9 : op 3 1 ≠ 1 := fun q => (c1266 op h) u8 u5 q
  have u10 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) u8 q a0 a2
  have u11 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u3 u9 q u10)
  have u12 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) u11 q
  have u13 : op 3 2 ≠ 1 := fun q => (chain op h.e677 1 3 3 2 1) u8 u11 q u5
  have u14 : op 3 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u1 u13 u12 q)
  have u15 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u9 u13
    u2)
  have u16 : op 3 0 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) q u14
  have u17 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 3) a0 q u14 u0
  have u18 : op 0 3 ≠ 0 := fun q => (chain op h.e677 3 3 0 0 1) a0 q u15 u10
  have u19 : op 0 3 ≠ 3 := fun q => (c1279 op h) a0 q u16
  exact (cellTotal (op 0 3)) u18 u7 u17 u19

theorem c1407 (op : Table) (h : Hyp op) :
    (op 1 3 ≠ 2) → (op 0 1 = 3) → (op 1 0 ≠ 3) → (op 1 1 = 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) a3 q
  have u3 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) a3 q
  have u4 : op 3 3 ≠ 0 := fun q => (c1406 op h) q a1 a2 a3 a0
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u4 q u1 u0)
  have u6 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 3 1) q a1 u5 u2
  have u7 : op 1 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u6 u3 a0 q)
  have u8 : op 3 1 = 3 := Classical.byContradiction (fun q => (c1280 op h) u5 u7 q)
  exact (chain op h.e677 1 3 3 3 1) u7 u8 u5 u2

theorem c1408 (op : Table) (h : Hyp op) :
    (op 0 1 = 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a1)
  have u1 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q u0
  have u2 : op 0 1 ≠ 0 := fun q => (cellUnique op 0 1 0 3 (by decide)) q a0
  have u3 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 3 (by decide)) q a0
  have u4 : op 2 0 ≠ 0 := fun q => (c1393 op h) q a0
  have u5 : op 1 0 ≠ 3 := fun q => (c1401 op h) q a0 a1
  have u6 : op 1 3 = 2 := Classical.byContradiction (fun q => (c1407 op h) q a0 u5 u0)
  have u7 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) q u6
  have u8 : op 1 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) q u1 u7 u5)
  have u9 : op 1 2 ≠ 0 := fun q => (rowUnique op h.inj 1 0 2 0 (by decide)) u8 q
  have u10 : op 0 0 ≠ 1 := fun q => (c1252 op h) q u2 u8
  have u11 : op 2 0 ≠ 1 := fun q => (c1404 op h) q a0 u5 u0
  have u12 : op 0 3 ≠ 1 := fun q => (c1405 op h) q a0 u5 u0
  have u13 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u10 u3 q
    u12)
  have u14 : op 0 2 ≠ 2 := fun q => (cellUnique op 0 2 1 2 (by decide)) u13 q
  have u15 : op 0 3 ≠ 2 := fun q => (chain op h.e677 1 0 0 3 2) u8 a0 q u9
  have u16 : op 2 0 ≠ 2 := fun q => (chain op h.e677 0 2 1 0 2) u13 u8 q u14
  have u17 : op 2 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u4 u11 u16 q)
  exact (chain op h.e677 0 2 1 0 3) u13 u8 u17 u15

theorem c1409 (op : Table) (h : Hyp op) :
    (op 0 0 ≠ 1) → (op 0 3 ≠ 1) → (op 1 0 = 0) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a3
  have u1 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u2 : op 0 1 ≠ 1 := fun q => (c1255 op h) q a0 a2
  have u3 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) a0 u2 q a1)
  have u4 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 0 3 0 (by decide)) a2 q
  have u5 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u1
  have u6 : op 1 2 ≠ 0 := fun q => (rowUnique op h.inj 1 0 2 0 (by decide)) a2 q
  have u7 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 0 0 2 1) a2 q u3 u5
  have u8 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u2 u7 u0)
  have u9 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q u8
  have u10 : op 0 0 ≠ 3 := fun q => (chain op h.e677 1 0 0 0 3) a2 u8 q u4
  have u11 : op 0 0 ≠ 2 := fun q => (chain op h.e677 1 0 0 0 2) a2 u8 q u6
  exact (cellTotal (op 0 0)) u9 a0 u11 u10

theorem c1410 (op : Table) (h : Hyp op) :
    (op 0 0 = 1) → (op 1 0 = 0) → (op 1 1 = 1) → False := by
  intro a0 a1 a2
  have u0 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) a0 q
  have u1 : op 0 1 ≠ 0 := fun q => (chain op h.e677 0 1 0 1 1) q a0 a2 u0
  exact (c1252 op h) a0 u1 a1

theorem c1411 (op : Table) (h : Hyp op) :
    (op 0 1 = 0) → (op 0 0 ≠ 1) → (op 1 0 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q a0
  have u1 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 0 3 0 (by decide)) a2 q
  have u2 : op 0 0 ≠ 3 := fun q => (chain op h.e677 1 0 0 0 3) a2 a0 q u1
  have u3 : op 0 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u0 a1 q u2)
  have u4 : op 1 2 ≠ 0 := fun q => (chain op h.e677 0 1 0 2 0) a0 u3 q a1
  exact (chain op h.e677 1 0 0 0 2) a2 a0 u3 u4

theorem c1412 (op : Table) (h : Hyp op) :
    (op 1 0 = 0) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a1
  have u2 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a1)
  have u3 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u2
  have u4 : op 1 3 ≠ 0 := fun q => (rowUnique op h.inj 1 0 3 0 (by decide)) a0 q
  have u5 : op 0 1 ≠ 1 := fun q => (c1258 op h) a0 q u3
  have u6 : op 0 0 ≠ 1 := fun q => (c1410 op h) q a0 u2
  have u7 : op 0 3 = 1 := Classical.byContradiction (fun q => (c1409 op h) u6 q a0 a1)
  have u8 : op 0 1 ≠ 0 := fun q => (c1411 op h) q u6 a0
  have u9 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u8 u5 q u1)
  have u10 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 1 3 (by decide)) u7 q
  have u11 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 1 2) q u7 u9 u0
  have u12 : op 3 0 ≠ 3 := fun q => (chain op h.e677 0 3 1 0 3) u7 a0 q u10
  have u13 : op 3 0 ≠ 1 := fun q => (chain op h.e677 0 3 1 0 1) u7 a0 q u1
  have u14 : op 3 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u11 u13 q u12)
  have u15 : op 0 2 ≠ 3 := fun q => (chain op h.e677 1 0 0 2 3) a0 u9 q u4
  exact (chain op h.e677 0 3 1 0 2) u7 a0 u14 u15

theorem c1413 (op : Table) (h : Hyp op) :
    (op 1 2 = 0) → (op 0 0 ≠ 1) → (op 0 1 ≠ 0) → (op 1 0 = 2) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) a3 q
  have u1 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) a3 q
  have u2 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a4
  have u3 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a4)
  have u4 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u3
  have u5 : op 0 1 ≠ 1 := fun q => (chain op h.e677 0 1 1 2 0) q a3 a0 a1
  have u6 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a2 u5 q u2)
  have u7 : op 0 0 ≠ 2 := fun q => (rowUnique op h.inj 0 0 1 2 (by decide)) q u6
  have u8 : op 2 2 ≠ 2 := fun q => (chain op h.e677 1 2 0 2 2) a0 u6 q u0
  have u9 : op 2 2 ≠ 1 := fun q => (chain op h.e677 1 2 0 2 1) a0 u6 q a4
  have u10 : op 2 2 ≠ 3 := fun q => (chain op h.e677 1 2 0 2 3) a0 u6 q u1
  have u11 : op 2 1 ≠ 1 := fun q => (chain op h.e677 2 1 1 0 2) q a0 a3 u9
  have u12 : op 2 2 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 2)) q u9 u8 u10)
  have u13 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 2 0 (by decide)) q u12
  have u14 : op 0 2 ≠ 1 := fun q => (chain op h.e677 0 2 1 2 0) q a3 u12 u7
  have u15 : op 0 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) a1 u5 u14
    q)
  have u16 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 0 2 3 1) a3 q u15 u4
  have u17 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u13 u11 q u16)
  exact (chain op h.e677 2 1 2 0 2) u17 u12 a3 u9

theorem c1414 (op : Table) (h : Hyp op) :
    (op 2 0 = 0) → (op 0 1 = 2) → (op 1 0 = 2) → False := by
  intro a0 a1 a2
  have u0 : op 2 2 ≠ 0 := fun q => (rowUnique op h.inj 2 0 2 0 (by decide)) a0 q
  have u1 : op 0 2 ≠ 1 := fun q => (chain op h.e677 2 0 0 1 2) a0 q a1 u0
  exact (chain op h.e677 0 1 2 0 2) a1 a0 a2 u1

theorem c1415 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 1) → (op 0 0 ≠ 1) → (op 0 1 ≠ 0) → (op 1 0 = 2) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 2 3 (by decide)) a3 q
  have u4 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) a3 q
  have u5 : op 1 2 ≠ 0 := fun q => (c1413 op h) q a1 a2 a3 a4
  have u6 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a4
  have u7 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a4
  have u8 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a4)
  have u9 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a2 a0 q u6)
  have u10 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u8
  have u11 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u8 q
  have u12 : op 2 0 ≠ 1 := fun q => (chain op h.e677 0 1 2 1 1) u9 q u8 a0
  have u13 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u7 u10 u5
    q)
  have u14 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 0 3 (by decide)) u13 q
  have u15 : op 3 2 ≠ 1 := fun q => (chain op h.e677 1 3 0 2 1) u13 u9 q u11
  have u16 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u3 u11 q
    u14)
  have u17 : op 3 2 ≠ 3 := fun q => (chain op h.e677 1 3 0 2 3) u13 u9 q u14
  have u18 : op 3 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u2 u15 q u17)
  have u19 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) q u18
  have u20 : op 2 0 ≠ 3 := fun q => (chain op h.e677 0 1 2 3 0) u9 q u13 a1
  have u21 : op 2 0 ≠ 0 := fun q => (c1414 op h) q u9 a3
  have u22 : op 2 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u21 u12 q u20)
  have u23 : op 3 1 ≠ 1 := fun q => (chain op h.e677 3 1 1 0 2) q u13 a3 u15
  have u24 : op 2 2 ≠ 2 := fun q => (rowUnique op h.inj 2 0 2 2 (by decide)) u22 q
  have u25 : op 2 3 = 2 := Classical.byContradiction (fun q => (c1287 op h) u24 q u18 u1)
  have u26 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 2 3 3 2) u16 q u25 u4
  have u27 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u26 u17
    u0)
  have u28 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u23 u19 u26)
  have u29 : op 3 3 ≠ 1 := fun q => (chain op h.e677 3 0 3 1 2) u27 q u9 u2
  have u30 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) u28 q
  exact (cellTotal (op 3 3)) u30 u29 u1 u0

theorem c1416 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 0) → (op 0 0 ≠ 1) → (op 1 0 = 2) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a3
  have u1 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u2 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u1
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u1 q
  have u4 : op 1 0 ≠ 3 := fun q => (cellUnique op 1 0 2 3 (by decide)) a2 q
  have u5 : op 1 2 ≠ 0 := fun q => (c1413 op h) q a1 a0 a2 a3
  have u6 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u0 u2 u5 q)
  have u7 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 0 3 (by decide)) u6 q
  have u8 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u4 u3 q u7)
  have u9 : op 0 1 = 1 := Classical.byContradiction (fun q => (c1415 op h) q a1 a0 a2 a3)
  have u10 : op 0 3 ≠ 1 := fun q => (rowUnique op h.inj 0 1 3 1 (by decide)) u9 q
  exact (chain op h.e677 0 1 1 2 3) u9 a2 u8 u10

theorem c1417 (op : Table) (h : Hyp op) :
    (op 1 2 ≠ 0) → (op 0 0 ≠ 1) → (op 1 0 ≠ 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a3
  have u3 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u4 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u3
  have u5 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u3 q
  have u6 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q u3
  have u7 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u2 u6 q a2)
  have u8 : op 0 1 = 0 := Classical.byContradiction (fun q => (c1416 op h) q a1 u7 a3)
  have u9 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q u8
  have u10 : op 1 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 0) u2 u4 a0
    q)
  have u11 : op 3 0 ≠ 1 := fun q => (chain op h.e677 1 3 0 0 1) u10 u8 q u5
  have u12 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 0 2 2 (by decide)) u7 q
  have u13 : op 2 1 ≠ 1 := fun q => (chain op h.e677 1 0 2 1 0) u7 q u8 u2
  have u14 : op 1 3 ≠ 3 := fun q => (cellUnique op 1 3 0 3 (by decide)) u10 q
  have u15 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) a2 u5 q
    u14)
  have u16 : op 3 0 ≠ 3 := fun q => (chain op h.e677 1 3 0 0 3) u10 u8 q u14
  have u17 : op 0 0 ≠ 3 := fun q => (chain op h.e677 0 1 0 3 0) u8 q u10 a1
  have u18 : op 0 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u9 a1 q u17)
  have u19 : op 3 0 ≠ 0 := fun q => (chain op h.e677 1 3 0 0 0) u10 u8 q a2
  have u20 : op 3 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 0)) u19 u11 q u16)
  have u21 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) u20 q
  have u22 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 0 2 0 2) u7 q u18 a0
  have u23 : op 0 3 = 1 := Classical.byContradiction (fun q => (chain op h.e677 0 1 0 2 3) u8 u18
    u15 q)
  have u24 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 0 2 0 2) u20 q u18 u1
  have u25 : op 2 3 ≠ 1 := fun q => (chain op h.e677 3 0 2 1 0) u20 q u8 u19
  have u26 : op 2 3 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) u24 u25 q u0)
  have u27 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 2 3 3 2) u15 q u26 u12
  have u28 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 0 2 3 1) u7 q u23 u4
  have u29 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u22 u13 q u28)
  have u30 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 2 3 1 2) u15 q u29 u12
  have u31 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u30 u21 u27)
  exact (chain op h.e677 3 1 0 1 1) u31 u23 u3 u30

theorem c1418 (op : Table) (h : Hyp op) :
    (op 0 0 ≠ 1) → (op 1 0 ≠ 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a2
  have u2 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a2)
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u2 q
  have u4 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q u2
  have u5 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u1 u4 q a1)
  have u6 : op 1 2 = 0 := Classical.byContradiction (fun q => (c1417 op h) q a0 a1 a2)
  have u7 : op 0 1 = 0 := Classical.byContradiction (fun q => (c1416 op h) q a0 u5 a2)
  have u8 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q u7
  have u9 : op 1 2 ≠ 3 := fun q => (cellUnique op 1 2 0 3 (by decide)) u6 q
  have u10 : op 1 3 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) a1 u3 u9
    q)
  have u11 : op 0 0 ≠ 2 := fun q => (chain op h.e677 0 1 0 2 0) u7 q u6 a0
  have u12 : op 0 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) u8 a0 u11 q)
  have u13 : op 3 0 ≠ 1 := fun q => (chain op h.e677 0 0 3 1 0) u12 q u7 u8
  have u14 : op 0 3 ≠ 0 := fun q => (rowUnique op h.inj 0 1 3 0 (by decide)) u7 q
  have u15 : op 3 1 ≠ 1 := fun q => (c1266 op h) u10 u3 q
  have u16 : op 0 3 = 1 := Classical.byContradiction (fun q => (chain op h.e677 0 1 0 3 3) u7 u12
    u10 q)
  have u17 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 1 1) q u16 u2 u15
  have u18 : op 3 0 ≠ 0 := fun q => (c1254 op h) u12 u14 q
  have u19 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u18 u17 u0
    q)
  have u20 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u19 q
  have u21 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) u10 q u19 a1
  have u22 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u13 u15 q
    u20)
  have u23 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u17 u15 q u21)
  exact (chain op h.e677 1 3 3 2 1) u10 u23 u22 u3

theorem c1419 (op : Table) (h : Hyp op) :
    (op 1 0 ≠ 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a1
  have u2 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a1
  have u3 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a1)
  have u4 : op 1 3 ≠ 1 := fun q => (rowUnique op h.inj 1 1 3 1 (by decide)) u3 q
  have u5 : op 0 0 = 1 := Classical.byContradiction (fun q => (c1418 op h) q a0 a1)
  have u6 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q u5
  have u7 : op 0 0 ≠ 3 := fun q => (cellUnique op 0 0 1 3 (by decide)) u5 q
  have u8 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) u5 q
  have u9 : op 0 1 ≠ 0 := fun q => (chain op h.e677 0 1 0 1 1) q u5 u3 u8
  have u10 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u9 u8 q u1)
  have u11 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 1 3 (by decide)) u3 q
  have u12 : op 1 0 ≠ 1 := fun q => (rowUnique op h.inj 1 0 1 1 (by decide)) q u3
  have u13 : op 1 0 = 2 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) u2 u12 q a0)
  have u14 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 0 3 2 (by decide)) u13 q
  have u15 : op 0 2 ≠ 0 := fun q => (chain op h.e677 0 0 1 2 0) u5 u13 q u6
  have u16 : op 0 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) u6 u9 u15
    q)
  have u17 : op 0 3 ≠ 3 := fun q => (cellUnique op 0 3 0 3 (by decide)) u16 q
  have u18 : op 3 1 ≠ 0 := fun q => (chain op h.e677 0 3 0 1 0) u16 u5 q u7
  have u19 : op 3 1 ≠ 3 := fun q => (chain op h.e677 0 3 0 1 3) u16 u5 q u17
  have u20 : op 3 1 ≠ 1 := fun q => (chain op h.e677 0 3 0 1 1) u16 u5 q u1
  have u21 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u18 u20 q u19)
  have u22 : op 3 0 ≠ 0 := fun q => (chain op h.e677 3 0 0 0 1) q u16 u5 u18
  have u23 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u22 u18 u0
    q)
  have u24 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u23 q
  have u25 : op 3 0 ≠ 1 := fun q => (chain op h.e677 3 3 0 0 1) u23 u16 q u19
  have u26 : op 3 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) u25 u20 q
    u24)
  have u27 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 2 1) q u21 u26 u11
  have u28 : op 1 3 ≠ 0 := fun q => (chain op h.e677 1 3 0 2 1) q u10 u26 u11
  exact (cellTotal (op 1 3)) u28 u4 u14 u27

theorem c1420 (op : Table) (h : Hyp op) :
    (op 0 0 = 1) → (op 0 1 ≠ 0) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) a0 q
  have u2 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a2)
  have u3 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a2)
  have u4 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a2
  have u5 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u3
  have u6 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a1 u1 q u4)
  have u7 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 1) u2 q a0 u5
  have u8 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 1 3 2 (by decide)) u6 q
  have u9 : op 0 0 ≠ 0 := fun q => (cellUnique op 0 0 0 1 (by decide)) q a0
  have u10 : op 0 0 ≠ 3 := fun q => (cellUnique op 0 0 1 3 (by decide)) a0 q
  have u11 : op 0 3 ≠ 1 := fun q => (rowUnique op h.inj 0 0 3 1 (by decide)) a0 q
  have u12 : op 0 3 ≠ 0 := fun q => (chain op h.e677 0 0 1 3 0) a0 u2 q u9
  have u13 : op 0 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u12 u11 u8 q)
  have u14 : op 3 0 ≠ 0 := fun q => (c1257 op h) u13 u10 q
  have u15 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u14 u7 u0
    q)
  have u16 : op 3 0 ≠ 3 := fun q => (chain op h.e677 0 3 3 3 0) u13 q u15 u10
  exact (c1279 op h) u15 u13 u16

theorem c1421 (op : Table) (h : Hyp op) :
    (op 0 3 ≠ 0) → (op 0 0 ≠ 0) → (op 0 1 ≠ 0) → (op 0 1 = 2) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 0 0 ≠ 2 := fun q => (rowUnique op h.inj 0 0 1 2 (by decide)) q a3
  have u3 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 1 3 2 (by decide)) a3 q
  have u4 : op 0 0 ≠ 1 := fun q => (c1420 op h) q a2 a4
  have u5 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a4)
  have u6 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a4)
  have u7 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a4
  have u8 : op 0 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) a1 u4 u2 q)
  have u9 : op 0 2 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 0) a1 a2 q a0)
  have u10 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 1 2 (by decide)) q a3
  have u11 : op 2 0 ≠ 1 := fun q => (chain op h.e677 0 1 2 1 1) a3 q u6 u10
  have u12 : op 0 3 ≠ 3 := fun q => (rowUnique op h.inj 0 0 3 3 (by decide)) u8 q
  have u13 : op 0 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) a0 q u3 u12)
  have u14 : op 3 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 1) u13 u5 q u7
  have u15 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u14 u1 u0)
  have u16 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u15 u5 u14
  have u17 : op 3 0 ≠ 3 := fun q => (chain op h.e677 0 0 3 3 1) u8 q u13 a2
  have u18 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u17 u16 q
    u0)
  have u19 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u18
  have u20 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 3 0 2) u18 u15 q u19
  have u21 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u18 u15 q u1
  have u22 : op 2 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) q u11 u20 u21)
  have u23 : op 3 0 = 2 := Classical.byContradiction (fun q => (chain op h.e677 3 2 3 0 0) u18 u15
    u22 q)
  exact (chain op h.e677 0 0 3 2 0) u8 u23 u9 a1

theorem c1422 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 1) → (op 0 0 ≠ 0) → (op 0 1 ≠ 0) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 0 0 ≠ 1 := fun q => (c1420 op h) q a2 a3
  have u3 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a3)
  have u4 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a3
  have u5 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a3)
  have u6 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a3
  have u7 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a2 a0 q u6)
  have u8 : op 0 0 ≠ 2 := fun q => (rowUnique op h.inj 0 0 1 2 (by decide)) q u7
  have u9 : op 2 0 ≠ 1 := fun q => (chain op h.e677 0 1 2 1 1) u7 q u5 a0
  have u10 : op 0 3 = 0 := Classical.byContradiction (fun q => (c1421 op h) q a1 a2 u7 a3)
  have u11 : op 0 0 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 0)) a1 u2 u8 q)
  have u12 : op 0 3 ≠ 1 := fun q => (cellUnique op 0 3 0 1 (by decide)) u10 q
  have u13 : op 0 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u2 a0 q
    u12)
  have u14 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 0 3 3 0) u3 q u10 u4
  have u15 : op 3 3 ≠ 1 := fun q => (chain op h.e677 0 3 0 3 1) u10 u11 q u6
  have u16 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u15 u1 u0)
  have u17 : op 3 0 ≠ 3 := fun q => (chain op h.e677 0 0 3 3 0) u11 q u10 a1
  have u18 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u17 u14 q
    u0)
  have u19 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u18
  have u20 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 3 0 2) u18 u16 q u19
  have u21 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u18 u16 q u1
  have u22 : op 2 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) q u9 u20 u21)
  have u23 : op 3 0 = 2 := Classical.byContradiction (fun q => (chain op h.e677 3 2 3 0 0) u18 u16
    u22 q)
  exact (chain op h.e677 0 0 3 2 1) u11 u23 u13 a2

theorem c1423 (op : Table) (h : Hyp op) :
    (op 0 1 = 1) → (op 0 0 ≠ 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 0 2 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) a0 q
  have u1 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a2)
  have u2 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a2)
  have u3 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) u1 q
  have u4 : op 1 3 ≠ 0 := fun q => (chain op h.e677 0 1 1 3 0) a0 u1 q a1
  have u5 : op 1 3 ≠ 2 := fun q => (chain op h.e677 0 1 1 3 2) a0 u1 q u0
  have u6 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u4 q u5 u3)
  exact (rowUnique op h.inj 1 1 3 1 (by decide)) u2 u6

theorem c1424 (op : Table) (h : Hyp op) :
    (op 0 3 = 1) → (op 0 0 ≠ 3) → (op 1 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a2)
  have u3 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a2
  have u4 : op 3 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 1) a0 u2 q u3
  have u5 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u4 u1 u0)
  exact (chain op h.e677 0 3 1 3 0) a0 u2 u5 a1

theorem c1425 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 0) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a1)
  have u2 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a1
  have u3 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a1
  have u4 : op 0 0 ≠ 1 := fun q => (c1420 op h) q a0 a1
  have u5 : op 0 1 ≠ 1 := fun q => (c1423 op h) q u4 a1
  have u6 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a0 u5 q u3)
  have u7 : op 0 0 = 0 := Classical.byContradiction (fun q => (c1422 op h) u5 q a0 a1)
  have u8 : op 0 3 ≠ 2 := fun q => (rowUnique op h.inj 0 1 3 2 (by decide)) u6 q
  have u9 : op 0 0 ≠ 3 := fun q => (cellUnique op 0 0 0 3 (by decide)) u7 q
  have u10 : op 0 3 ≠ 1 := fun q => (c1424 op h) q u9 a1
  have u11 : op 0 3 ≠ 0 := fun q => (rowUnique op h.inj 0 0 3 0 (by decide)) u7 q
  have u12 : op 0 3 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u11 u10 u8 q)
  have u13 : op 3 1 ≠ 0 := fun q => (chain op h.e677 1 0 3 0 0) u1 q u7 u2
  have u14 : op 3 0 ≠ 0 := fun q => (c1257 op h) u12 u9 q
  have u15 : op 3 3 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) u14 u13 u0
    q)
  have u16 : op 3 0 = 3 := Classical.byContradiction (fun q => (c1279 op h) u15 u12 q)
  exact (chain op h.e677 0 3 3 3 0) u12 u16 u15 u9

theorem c1426 (op : Table) (h : Hyp op) :
    (op 0 2 = 1) → (op 1 1 ≠ 2) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 2 3 ≠ 3 := fun q => (c1340 op h) q
  have u2 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u3 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a1)
  have u4 : op 0 1 = 0 := Classical.byContradiction (fun q => (c1425 op h) q a1)
  have u5 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a1)
  have u6 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a1
  have u7 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 0 3 1 0) u3 q u4 u6
  have u8 : op 0 2 ≠ 2 := fun q => (cellUnique op 0 2 1 2 (by decide)) a0 q
  have u9 : op 2 3 ≠ 2 := fun q => (chain op h.e677 0 2 1 3 2) a0 u3 q u8
  have u10 : op 0 1 ≠ 2 := fun q => (cellUnique op 0 1 0 2 (by decide)) u4 q
  have u11 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 1 (by decide)) q u5
  have u12 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 0 3 2 1) u3 q a0 u11
  have u13 : op 2 3 ≠ 1 := fun q => (chain op h.e677 0 2 1 3 1) a0 u3 q u10
  have u14 : op 2 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 3)) q u13 u9 u1)
  have u15 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 1 3 0 (by decide)) q u14
  have u16 : op 3 1 ≠ 3 := fun q => (chain op h.e677 2 3 0 1 3) u14 a0 q u1
  have u17 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u7 u12 u16)
  have u18 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 1 0 (by decide)) q u17
  have u19 : op 3 3 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) u17 q
  have u20 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u19 q u2 u0)
  have u21 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 0) q u20 u4 u18
  have u22 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u21 u16 q
    u0)
  have u23 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u22
  have u24 : op 2 1 ≠ 2 := fun q => (chain op h.e677 3 2 3 1 2) u22 u20 q u23
  have u25 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 3 1 3) u22 u20 q u2
  have u26 : op 2 1 ≠ 1 := fun q => (chain op h.e677 3 2 3 1 1) u22 u20 q u12
  exact (cellTotal (op 2 1)) u15 u26 u24 u25

theorem c1427 (op : Table) (h : Hyp op) :
    (op 1 1 ≠ 2) → False := by
  intro a0
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 0 2 ≠ 1 := fun q => (c1426 op h) q a0
  have u3 : op 0 1 = 0 := Classical.byContradiction (fun q => (c1425 op h) q a0)
  have u4 : op 1 1 = 1 := Classical.byContradiction (fun q => (c1390 op h) q a0)
  have u5 : op 0 1 ≠ 3 := fun q => (c1408 op h) q a0
  have u6 : op 1 0 ≠ 0 := fun q => (c1412 op h) q a0
  have u7 : op 1 0 = 3 := Classical.byContradiction (fun q => (c1419 op h) q a0)
  have u8 : op 0 1 ≠ 1 := fun q => (cellUnique op 0 1 0 1 (by decide)) u3 q
  have u9 : op 0 0 ≠ 0 := fun q => (rowUnique op h.inj 0 0 1 0 (by decide)) q u3
  have u10 : op 3 1 ≠ 1 := fun q => (chain op h.e677 1 0 3 1 0) u7 q u3 u6
  have u11 : op 0 0 ≠ 1 := fun q => (chain op h.e677 0 1 0 1 1) u3 q u4 u8
  have u12 : op 0 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 0 1) u11 u8 u2
    q)
  have u13 : op 3 1 ≠ 0 := fun q => (chain op h.e677 3 1 0 1 1) q u12 u4 u10
  have u14 : op 3 3 ≠ 1 := fun q => (chain op h.e677 0 3 1 3 1) u12 u7 q u5
  have u15 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u14 u1 u0)
  have u16 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u15 u7 u14
  have u17 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u13 u10 q u16)
  have u18 : op 0 0 = 3 := Classical.byContradiction (fun q => (c1424 op h) u12 q a0)
  have u19 : op 3 2 = 3 := Classical.byContradiction (fun q => (chain op h.e677 3 3 0 1 2) u15 u12
    u17 q)
  have u20 : op 3 2 ≠ 1 := fun q => (cellUnique op 3 2 1 3 (by decide)) q u19
  have u21 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u10 u20
    u14)
  exact (chain op h.e677 0 0 3 1 0) u18 u21 u3 u9

theorem c1438 (op : Table) (h : Hyp op) :
    (op 0 1 = 3) → (op 1 3 ≠ 3) → (op 3 1 = 0) → (op 3 3 ≠ 0) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u4 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u2 q
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) a3 q u1 u0)
  have u6 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u5
  have u7 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u5 u2 u6
  have u8 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) q u5 a0 a3
  have u9 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u8 u7 q u0)
  have u10 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u2 u9 a1
  have u11 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u10 u4 a1)
  exact (chain op h.e677 1 3 0 3 1) u11 a0 u5 u3

theorem c1439 (op : Table) (h : Hyp op) :
    (op 3 3 ≠ 0) → (op 0 1 ≠ 0) → (op 0 2 = 1) → (op 1 0 = 3) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u4 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q u3
  have u5 : op 0 1 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) q a2
  have u6 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 0 3 2 1) a3 q a2 u4
  have u7 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a3 q
  have u8 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) a0 q u1 u0)
  have u9 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u8
  have u10 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u8
  have u11 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u8 u3 u10
  have u12 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u9 u6 u11)
  have u13 : op 0 1 ≠ 3 := fun q => (c1438 op h) q u7 u12 a0
  have u14 : op 0 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) a1 u5 q u13)
  have u15 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 2) q u8 u14 u2
  have u16 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u15 u11 q
    u0)
  have u17 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u16
  have u18 : op 2 1 ≠ 2 := fun q => (chain op h.e677 3 2 3 1 2) u16 u8 q u17
  have u19 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 3 1 3) u16 u8 q u1
  have u20 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u3 u16 u7
  have u21 : op 2 1 ≠ 1 := fun q => (chain op h.e677 3 2 3 1 1) u16 u8 q u6
  have u22 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 3) u3 q a3 u20
  exact (cellTotal (op 2 1)) u22 u21 u18 u19

theorem c1440 (op : Table) (h : Hyp op) :
    (op 3 3 = 0) → (op 1 0 = 3) → (op 3 1 ≠ 2) → False := by
  intro a0 a1 a2
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u2 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u1 q
  have u3 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a0 q
  have u4 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a0
  have u5 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q a0 a1 u3
  have u6 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 0 2 3 (by decide)) a1 q
  have u7 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a1 q
  have u8 : op 3 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u4 q a2 u5)
  have u9 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) u8 q
  have u10 : op 1 3 ≠ 0 := fun q => (chain op h.e677 3 1 1 0 3) u8 q a1 u3
  have u11 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u10 q u2 u7)
  have u12 : op 3 2 ≠ 2 := fun q => (chain op h.e677 1 3 1 2 2) u11 u1 q u6
  have u13 : op 3 2 ≠ 3 := fun q => (chain op h.e677 1 3 1 2 3) u11 u1 q u7
  exact (cellTotal (op 3 2)) u0 u9 u12 u13

theorem c1441 (op : Table) (h : Hyp op) :
    (op 0 2 = 1) → (op 1 0 = 3) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q u2
  have u4 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a1 q
  have u5 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 0 3 2 1) a1 q a0 u3
  have u6 : op 3 3 ≠ 0 := fun q => (c1440 op h) q a1 u5
  have u7 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u6 q u1 u0)
  have u8 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u7
  have u9 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u7
  have u10 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u7 u2 u9
  have u11 : op 3 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) q u8 u5 u10)
  have u12 : op 0 1 = 0 := Classical.byContradiction (fun q => (c1439 op h) u6 q a0 a1)
  have u13 : op 3 0 ≠ 0 := fun q => (rowUnique op h.inj 3 0 1 0 (by decide)) q u11
  have u14 : op 3 0 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 0) q u7 u12 u13
  have u15 : op 3 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) u14 u10 q
    u0)
  have u16 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u15
  have u17 : op 2 1 ≠ 2 := fun q => (chain op h.e677 3 2 3 1 2) u15 u7 q u16
  have u18 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 3 1 3) u15 u7 q u1
  have u19 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u2 u15 u4
  have u20 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 3) u2 q a1 u19
  have u21 : op 2 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u20 q u17 u18)
  exact (chain op h.e677 3 2 3 1 1) u15 u7 u21 u5

theorem c1442 (op : Table) (h : Hyp op) :
    (op 3 1 = 0) → (op 0 1 ≠ 1) → (op 1 0 = 3) → (op 3 2 ≠ 1) → False := by
  intro a0 a1 a2 a3
  have u0 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u1 : op 1 1 ≠ 0 := fun q => (cellUnique op 1 1 0 2 (by decide)) q u0
  have u2 : op 0 2 ≠ 1 := fun q => (c1441 op h) q a2
  have u3 : op 0 0 ≠ 1 := fun q => (chain op h.e677 1 0 3 0 1) a2 a0 q u1
  have u4 : op 0 3 ≠ 1 := fun q => (chain op h.e677 3 1 0 1 2) a0 q u0 a3
  exact (rowTotal op h.surj 0 1) u3 a1 u2 u4

theorem c1443 (op : Table) (h : Hyp op) :
    (op 3 3 ≠ 0) → (op 0 1 ≠ 1) → (op 1 0 = 3) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u4 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u3 q
  have u5 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) a0 q u1 u0)
  have u6 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a2 q
  have u7 : op 3 2 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) q u5
  have u8 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u5 u3 u7
  have u9 : op 3 1 ≠ 0 := fun q => (c1442 op h) q a1 a2 u7
  have u10 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 3 1 (by decide)) q u5
  have u11 : op 3 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u9 u10 q u8)
  have u12 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) u11 q
  have u13 : op 3 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u2 u7 u12 q)
  have u14 : op 3 0 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) q u13
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u3 u13 u6
  have u16 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u15 u4 u6)
  have u17 : op 3 0 = 0 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 0) q u9 u2
    a0)
  exact (chain op h.e677 3 3 1 0 0) u5 u16 u17 u14

theorem c1444 (op : Table) (h : Hyp op) :
    (op 3 2 ≠ 1) → (op 1 0 = 3) → (op 3 3 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u2
  have u4 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u5 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u2 q
  have u6 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a2 q
  have u7 : op 3 1 = 2 := Classical.byContradiction (fun q => (c1440 op h) a2 a1 q)
  have u8 : op 1 0 ≠ 1 := fun q => (cellUnique op 1 0 1 3 (by decide)) q a1
  have u9 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a1 q
  have u10 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u7
  have u11 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) q u7
  have u12 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) u7 q
  have u13 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 1 2 0 3) u7 q a1 u6
  have u14 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u10 a0
    u6)
  have u15 : op 3 2 = 3 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u1 a0 u12 q)
  have u16 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u15 a2 q u0
  have u17 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 3 0 2) u15 a2 q u12
  have u18 : op 2 0 ≠ 0 := fun q => (chain op h.e677 3 2 3 0 0) u15 a2 q u11
  have u19 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u2 u15 u9
  have u20 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u18 q u17 u16)
  have u21 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u19 u5 u9)
  have u22 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u8 u3 q
    u19)
  have u23 : op 0 1 ≠ 3 := fun q => (chain op h.e677 2 0 1 1 3) u20 u22 q u13
  have u24 : op 0 2 ≠ 1 := fun q => (c1441 op h) q a1
  have u25 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 3) u2 q a1 u19
  have u26 : op 0 1 ≠ 1 := fun q => (chain op h.e677 2 0 1 1 1) u20 u22 q u25
  have u27 : op 0 1 ≠ 2 := fun q => (chain op h.e677 0 1 2 1 2) q u20 u2 u24
  have u28 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u26 u27 u23)
  exact (chain op h.e677 1 3 0 0 1) u21 u28 u14 u4

theorem c1445 (op : Table) (h : Hyp op) :
    (op 0 1 ≠ 1) → (op 1 0 = 3) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u2 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u1
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u1 q
  have u4 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u1 q
  have u5 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a1 q
  have u6 : op 1 0 ≠ 1 := fun q => (cellUnique op 1 0 1 3 (by decide)) q a1
  have u7 : op 3 3 = 0 := Classical.byContradiction (fun q => (c1443 op h) q a0 a1)
  have u8 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) u7 q
  have u9 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 3) q u7 a1 u8
  have u10 : op 3 1 = 2 := Classical.byContradiction (fun q => (c1440 op h) u7 a1 q)
  have u11 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) q u10
  have u12 : op 3 2 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) u10 q
  have u13 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1444 op h) q a1 u7)
  have u14 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 1 3 (by decide)) u13 q
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) q u1 u13 u3
  have u16 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u9 u14
    u0)
  have u17 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u15 u4 u5)
  have u18 : op 1 2 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u6 u2 q
    u15)
  have u19 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 3 0 2 1) u17 q u13 u3
  have u20 : op 0 1 ≠ 0 := fun q => (chain op h.e677 1 3 0 0 3) u17 q u16 u5
  have u21 : op 0 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) u20 a0 u19 q)
  have u22 : op 2 3 ≠ 0 := fun q => (chain op h.e677 3 1 2 0 3) u10 q a1 u8
  have u23 : op 2 0 ≠ 3 := fun q => (chain op h.e677 2 0 3 1 3) q u13 u21 u22
  have u24 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 1 0 2) u13 u17 q u12
  have u25 : op 2 0 ≠ 0 := fun q => (chain op h.e677 3 2 1 0 0) u13 u17 q u11
  have u26 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u25 q u24 u23)
  exact (chain op h.e677 2 0 1 1 3) u26 u18 u21 u22

theorem c1446 (op : Table) (h : Hyp op) :
    (op 1 0 = 3) → False := by
  intro a0
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u2 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u1 q
  have u3 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u1 q
  have u4 : op 1 2 ≠ 3 := fun q => (rowUnique op h.inj 1 0 2 3 (by decide)) a0 q
  have u5 : op 1 3 ≠ 3 := fun q => (rowUnique op h.inj 1 0 3 3 (by decide)) a0 q
  have u6 : op 0 1 = 1 := Classical.byContradiction (fun q => (c1445 op h) q a0)
  have u7 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) q u6
  have u8 : op 1 3 ≠ 0 := fun q => (chain op h.e677 0 1 1 3 0) u6 a0 q u7
  have u9 : op 1 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) u8 q u3 u5)
  have u10 : op 3 2 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) u9 u1 q u2
  have u11 : op 3 2 ≠ 3 := fun q => (chain op h.e677 1 3 1 2 3) u9 u1 q u5
  have u12 : op 3 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u0 u10 q u11)
  exact (chain op h.e677 1 3 1 2 2) u9 u1 u12 u4

theorem c1447 (op : Table) (h : Hyp op) :
    (op 0 1 = 1) → False := by
  intro a0
  have u0 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u1 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 1 2 (by decide)) q u0
  have u2 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u3 : op 0 0 ≠ 1 := fun q => (rowUnique op h.inj 0 0 1 1 (by decide)) q a0
  have u4 : op 0 2 ≠ 1 := fun q => (rowUnique op h.inj 0 1 2 1 (by decide)) a0 q
  have u5 : op 1 0 ≠ 1 := fun q => (chain op h.e677 0 1 1 1 2) a0 q u0 u4
  have u6 : op 1 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) q u5 u1 u2)
  exact (c1255 op h) a0 u3 u6

theorem c1448 (op : Table) (h : Hyp op) :
    (op 3 1 ≠ 3) → (op 0 3 ≠ 2) → (op 3 1 ≠ 2) → (op 3 2 ≠ 3) → (op 3 3 = 0) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u1 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u0
  have u2 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u0 q
  have u3 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 1 2 (by decide)) q u0
  have u4 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) u0 q
  have u5 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u0 q
  have u6 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u7 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a4 q
  have u8 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a4
  have u9 : op 3 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u8 q a2 a0)
  have u10 : op 1 3 ≠ 3 := fun q => (c1277 op h) u9 q u7
  have u11 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u6 u2 q
    u10)
  have u12 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u11
  have u13 : op 2 1 ≠ 2 := fun q => (chain op h.e677 1 2 3 1 2) u11 u9 q u4
  have u14 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 2 3 1 3) u11 u9 q u5
  have u15 : op 2 1 ≠ 1 := fun q => (c1263 op h) u0 u12 q
  have u16 : op 2 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) q u15 u13 u14)
  have u17 : op 1 0 ≠ 1 := fun q => (chain op h.e677 1 1 2 0 1) u0 u16 q u1
  have u18 : op 1 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) q u17 u3 u6)
  exact (chain op h.e677 1 1 2 0 0) u0 u16 u18 u17

theorem c1449 (op : Table) (h : Hyp op) :
    (op 0 3 ≠ 2) → (op 3 1 ≠ 2) → (op 3 2 ≠ 3) → (op 3 3 = 0) → False := by
  intro a0 a1 a2 a3
  have u0 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u1 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u2
  have u4 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u5 : op 1 0 ≠ 2 := fun q => (rowUnique op h.inj 1 0 1 2 (by decide)) q u2
  have u6 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) u2 q
  have u7 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u8 : op 3 1 = 3 := Classical.byContradiction (fun q => (c1448 op h) q a0 a1 a2 a3)
  have u9 : op 1 3 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) q u8 a3 u7
  have u10 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u7 u4 q
    u9)
  have u11 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u10
  have u12 : op 2 1 ≠ 1 := fun q => (c1263 op h) u2 u11 q
  have u13 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 3 (by decide)) q u8
  have u14 : op 1 0 ≠ 1 := fun q => (chain op h.e677 3 1 3 0 1) u8 a3 q u13
  have u15 : op 1 3 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) u14 u3 u11
    q)
  have u16 : op 3 2 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) u15 u2 q u4
  have u17 : op 3 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u1 u16 q a2)
  have u18 : op 2 3 ≠ 2 := fun q => (chain op h.e677 1 2 3 3 2) u10 u8 q u6
  have u19 : op 1 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 0)) q u14 u5 u7)
  have u20 : op 2 1 ≠ 3 := fun q => (chain op h.e677 1 1 2 3 1) u2 q u15 u3
  have u21 : op 2 2 = 2 := Classical.byContradiction (fun q => (c1287 op h) q u18 u17 u0)
  have u22 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 0) u2 q u19 u14
  have u23 : op 2 1 = 2 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u22 u12 q u20)
  exact (rowUnique op h.inj 2 1 2 2 (by decide)) u23 u21

theorem c1450 (op : Table) (h : Hyp op) :
    (op 3 2 ≠ 3) → (op 3 2 ≠ 1) → (op 3 3 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u1 : op 3 2 = 2 := Classical.byContradiction (fun q => (cellTotal (op 3 2)) u0 a1 q a0)
  have u2 : op 3 1 ≠ 2 := fun q => (rowUnique op h.inj 3 1 2 2 (by decide)) q u1
  have u3 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 2) a2 q u1 a0
  exact (c1449 op h) u3 u2 a0 a2

theorem c1451 (op : Table) (h : Hyp op) :
    (op 3 1 ≠ 2) → (op 3 2 ≠ 1) → (op 3 3 = 0) → False := by
  intro a0 a1 a2
  have u0 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u1 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u2 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u1 q
  have u3 : op 1 2 ≠ 2 := fun q => (rowUnique op h.inj 1 1 2 2 (by decide)) u1 q
  have u4 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u1 q
  have u5 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u6 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a2 q
  have u7 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a2
  have u8 : op 3 2 = 3 := Classical.byContradiction (fun q => (c1450 op h) q a1 a2)
  have u9 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u8
  have u10 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u8 a2 q u0
  have u11 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 3 0 2) u8 a2 q u9
  have u12 : op 2 0 ≠ 1 := fun q => (chain op h.e677 3 2 3 0 1) u8 a2 q a0
  have u13 : op 2 0 = 0 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) q u12 u11 u10)
  have u14 : op 3 1 ≠ 3 := fun q => (rowUnique op h.inj 3 1 2 3 (by decide)) q u8
  have u15 : op 3 1 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 1)) u7 q a0 u14)
  have u16 : op 2 1 ≠ 0 := fun q => (rowUnique op h.inj 2 0 1 0 (by decide)) u13 q
  have u17 : op 1 3 ≠ 3 := fun q => (c1277 op h) u15 q u6
  have u18 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u5 u2 q
    u17)
  have u19 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u18
  have u20 : op 2 1 ≠ 1 := fun q => (c1263 op h) u1 u19 q
  have u21 : op 2 1 ≠ 2 := fun q => (chain op h.e677 1 2 3 1 2) u18 u15 q u3
  have u22 : op 2 1 = 3 := Classical.byContradiction (fun q => (cellTotal (op 2 1)) u16 u20 u21 q)
  exact (chain op h.e677 1 2 3 1 3) u18 u15 u22 u4

theorem c1452 (op : Table) (h : Hyp op) :
    (op 3 3 = 0) → (op 3 2 ≠ 1) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u2
  have u4 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u5 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u6 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q a0
  have u7 : op 3 3 ≠ 1 := fun q => (cellUnique op 3 3 0 1 (by decide)) a0 q
  have u8 : op 3 1 = 2 := Classical.byContradiction (fun q => (c1451 op h) q a1 a0)
  have u9 : op 3 2 = 3 := Classical.byContradiction (fun q => (c1450 op h) q a1 a0)
  have u10 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q u9
  have u11 : op 3 1 ≠ 1 := fun q => (cellUnique op 3 1 1 2 (by decide)) q u8
  have u12 : op 3 1 ≠ 3 := fun q => (cellUnique op 3 1 2 3 (by decide)) u8 q
  have u13 : op 3 0 ≠ 2 := fun q => (rowUnique op h.inj 3 0 1 2 (by decide)) q u8
  have u14 : op 3 0 ≠ 3 := fun q => (rowUnique op h.inj 3 0 2 3 (by decide)) q u9
  have u15 : op 2 0 ≠ 3 := fun q => (chain op h.e677 3 2 3 0 3) u9 a0 q u1
  have u16 : op 2 0 ≠ 2 := fun q => (chain op h.e677 3 2 3 0 2) u9 a0 q u10
  have u17 : op 2 0 ≠ 0 := fun q => (chain op h.e677 3 2 3 0 0) u9 a0 q u13
  have u18 : op 0 3 ≠ 2 := fun q => (chain op h.e677 3 3 0 2 3) a0 q u9 u0
  have u19 : op 3 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 1) q u11 a1
    u7)
  have u20 : op 0 3 ≠ 3 := fun q => (c1279 op h) a0 q u14
  have u21 : op 2 0 = 1 := Classical.byContradiction (fun q => (cellTotal (op 2 0)) u17 q u16 u15)
  have u22 : op 0 3 ≠ 0 := fun q => (chain op h.e677 3 3 0 0 1) a0 q u19 u12
  have u23 : op 0 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 0 3)) u22 q u18 u20)
  have u24 : op 1 3 ≠ 3 := fun q => (chain op h.e677 3 0 1 3 1) u19 q u23 u6
  have u25 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u5 u4 q
    u24)
  have u26 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u2 u9 u24
  have u27 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u25
  have u28 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u3 u27
    u26)
  have u29 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 1) u2 q u28 u3
  exact (chain op h.e677 2 0 1 3 1) u21 u25 u23 u29

theorem c1453 (op : Table) (h : Hyp op) :
    (op 3 2 = 3) → (op 3 2 ≠ 1) → False := by
  intro a0 a1
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u2
  have u4 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u5 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u6 : op 3 3 ≠ 0 := fun q => (c1452 op h) q a1
  have u7 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u6 q u1 u0)
  have u8 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u7 u2 a1
  have u9 : op 3 2 ≠ 2 := fun q => (cellUnique op 3 2 2 3 (by decide)) q a0
  have u10 : op 2 1 ≠ 3 := fun q => (chain op h.e677 3 2 3 1 3) a0 u7 q u1
  have u11 : op 2 1 ≠ 2 := fun q => (chain op h.e677 3 2 3 1 2) a0 u7 q u9
  have u12 : op 1 3 ≠ 3 := fun q => (c1280 op h) u7 q u8
  have u13 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u5 u4 q
    u12)
  have u14 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u13
  have u15 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 3) q u2 a0 u12
  have u16 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u3 u14
    u15)
  have u17 : op 2 1 ≠ 1 := fun q => (c1263 op h) u2 u14 q
  have u18 : op 2 1 ≠ 0 := fun q => (chain op h.e677 1 1 2 0 1) u2 q u16 u3
  exact (cellTotal (op 2 1)) u18 u17 u11 u10

theorem c1454 (op : Table) (h : Hyp op) :
    (op 3 2 ≠ 1) → False := by
  intro a0
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 3 2 ≠ 0 := fun q => (c1367 op h) q
  have u3 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u4 : op 0 1 ≠ 1 := fun q => (c1447 op h) q
  have u5 : op 3 2 ≠ 3 := fun q => (c1453 op h) q a0
  have u6 : op 3 3 ≠ 0 := fun q => (c1452 op h) q a0
  have u7 : op 3 3 = 1 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) u6 q u1 u0)
  have u8 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 1 2) q u7 u3 a0
  have u9 : op 3 0 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 3 3) q u8 u5 u0)
  have u10 : op 3 0 ≠ 0 := fun q => (cellUnique op 3 0 0 3 (by decide)) q u9
  have u11 : op 0 1 ≠ 3 := fun q => (chain op h.e677 3 0 3 1 3) u9 u7 q u6
  have u12 : op 0 1 ≠ 2 := fun q => (chain op h.e677 3 0 3 1 2) u9 u7 q u2
  have u13 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u4 u12 u11)
  exact (chain op h.e677 3 0 3 1 0) u9 u7 u13 u10

theorem c1464 (op : Table) (h : Hyp op) :
    (op 1 3 ≠ 3) → False := by
  intro a0
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 1 := fun q => (cellUnique op 1 1 1 2 (by decide)) q u2
  have u4 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u5 : op 1 3 ≠ 2 := fun q => (rowUnique op h.inj 1 1 3 2 (by decide)) u2 q
  have u6 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u7 : op 0 1 ≠ 1 := fun q => (c1447 op h) q
  have u8 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1454 op h) q)
  have u9 : op 3 2 ≠ 3 := fun q => (cellUnique op 3 2 1 3 (by decide)) u8 q
  have u10 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u8
  have u11 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u8 q
  have u12 : op 1 3 ≠ 1 := fun q => (chain op h.e677 1 3 1 2 1) q u2 u8 u4
  have u13 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u11 u1 u0)
  have u14 : op 1 2 = 3 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 3) u6 u4 q
    a0)
  have u15 : op 1 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 1 3)) q u12 u5 a0)
  have u16 : op 1 2 ≠ 1 := fun q => (cellUnique op 1 2 1 3 (by decide)) q u14
  have u17 : op 0 1 ≠ 2 := fun q => (chain op h.e677 1 3 0 2 1) u15 q u8 u4
  have u18 : op 0 1 ≠ 3 := fun q => (chain op h.e677 1 3 0 3 0) u15 q u13 u6
  have u19 : op 1 0 = 1 := Classical.byContradiction (fun q => (rowTotal op h.surj 1 1) q u3 u16
    u12)
  have u20 : op 0 1 = 0 := Classical.byContradiction (fun q => (cellTotal (op 0 1)) q u7 u17 u18)
  have u21 : op 3 1 ≠ 3 := fun q => (chain op h.e677 3 1 3 0 1) q u13 u19 u10
  have u22 : op 3 0 ≠ 3 := fun q => (chain op h.e677 1 3 0 0 3) u15 u20 q a0
  exact (rowTotal op h.surj 3 3) u22 u21 u9 u0

/-- Refutes every E677 table on four elements, without symmetry breaking.
Final empty clause 1475; ordinary kernel-checked implication proof. -/
theorem no_e677_table (op : Table) (h : Hyp op) :
    False := by
  have u0 : op 3 3 ≠ 3 := fun q => (c1335 op h) q
  have u1 : op 3 3 ≠ 2 := fun q => (c1360 op h) q
  have u2 : op 1 1 = 2 := Classical.byContradiction (fun q => (c1427 op h) q)
  have u3 : op 1 1 ≠ 3 := fun q => (cellUnique op 1 1 2 3 (by decide)) u2 q
  have u4 : op 1 0 ≠ 3 := fun q => (c1446 op h) q
  have u5 : op 3 2 = 1 := Classical.byContradiction (fun q => (c1454 op h) q)
  have u6 : op 3 1 ≠ 1 := fun q => (rowUnique op h.inj 3 1 2 1 (by decide)) q u5
  have u7 : op 3 3 ≠ 1 := fun q => (rowUnique op h.inj 3 2 3 1 (by decide)) u5 q
  have u8 : op 3 3 = 0 := Classical.byContradiction (fun q => (cellTotal (op 3 3)) q u7 u1 u0)
  have u9 : op 3 1 ≠ 0 := fun q => (rowUnique op h.inj 3 1 3 0 (by decide)) q u8
  have u10 : op 1 3 = 3 := Classical.byContradiction (fun q => (c1464 op h) q)
  have u11 : op 3 1 ≠ 3 := fun q => (chain op h.e677 1 3 3 3 0) u10 q u8 u4
  have u12 : op 3 1 ≠ 2 := fun q => (chain op h.e677 1 3 3 2 1) u10 q u5 u3
  exact (cellTotal (op 3 1)) u9 u6 u12 u11

end E677Finite4

theorem solution :
∀ op : Fin 4 → Fin 4 → Fin 4, ¬ FiniteMagmaE677.E677 op := by
  intro op h
  have hs : ∀ i : Fin 4, Function.Surjective (op i) := fun i x => ⟨_, (h x i).symm⟩
  exact E677Finite4.no_e677_table op
    { inj := fun i => Finite.injective_iff_surjective.mpr (hs i)
      surj := hs
      e677 := h }

#print axioms solution
