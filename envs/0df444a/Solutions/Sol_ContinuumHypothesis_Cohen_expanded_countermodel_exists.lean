-- Prove2me | solution 1 for ContinuumHypothesis.Cohen.expanded_countermodel_exists
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:12:09.209224+00:00
-- url     : https://prove2.me/submissions/b3ffea4e-9bd8-41d8-a293-937ddd2ebdcf

import Definitions.Def_CH_Cohen_Library10
import Theorems.Thm_bSet_neg_CH
import Theorems.Thm_bSet_models_ZFC
/-
Physical source: Flypitch, Jesse Han and Floris van Doorn (Apache-2.0).
Lean 4 port: Ian Klatzco, with Claude.
Upstream commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Original notices and source statements are retained.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/- Source module: Definitions.Flypitch4.ToMathlib -/
section CohenSource_ToMathlib
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/











set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2 sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`, `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4 has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported, prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`, `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3 proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc., translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra` (src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/

/-!
## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No redeclaration needed.
-/

/-! ## dvector type and namespace -/







namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

































































































































end DVec

/-! ## set namespace -/

namespace Set









-- subset_sInter_iff is already in Mathlib as Set.subset_sInter_iff



end Set

/-! ## topological_space section -/

section TopologicalSpace

open TopologicalSpace Set Filter

variable {α : Type u} {β : Type v}
variable [t : TopologicalSpace α] [TopologicalSpace β]











end TopologicalSpace

/-! ## ordinal namespace -/

namespace Ordinal

variable {σ : Type*}





end Ordinal

/-! ## cardinal namespace -/

namespace Cardinal

open scoped Cardinal

-- Note: Cardinal.mk_union_le already exists in mathlib4 (explicit args version).
-- Downstream files use `mk_union_le` with implicit args; that's directly served
-- by the mathlib4 version since Lean can infer the args. No redeclaration needed.
-- The alias below makes it available for direct call without name conflicts:










end Cardinal

/-! ## nat namespace -/

namespace Nat





end Nat

/-! ## classical namespace (logic helpers) -/

namespace Classical











end Classical

/-! ## list namespace -/

namespace List







end List

/-! ## additional nat lemmas -/

namespace Nat



end Nat

/-! ## misc prop lemmas -/





/-! ## additional set lemmas -/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}



























end Set

/-! ## nonempty namespace -/

namespace Nonempty

variable {α : Sort u} {β : Sort v}



end Nonempty

/-! ## arity' type and namespace -/



namespace Arity'

































end Arity'

/-! ## Miscellaneous lemmas -/



/-! ## Boolean algebra / lattice helpers -/













-- iSup/iInf distributivity (aliases for Lean 4 mathlib names)
private theorem inf_iSup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊓ (⨆ (i : ι), s i) = ⨆ (i : ι), a ⊓ s i :=
  inf_iSup_eq a s

private theorem iSup_inf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨆ (i : ι), s i) ⊓ a = ⨆ (i : ι), (s i ⊓ a) := by
  rw [inf_comm, inf_iSup_eq']; simp_rw [inf_comm]





-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.




-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4












open scoped Flypitch




























-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version



private theorem inf_eq_of_le {α : Type*} [DistribLattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  le_antisymm inf_le_left (le_inf le_rfl h)



private theorem le_of_sub_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b := by
  rw [inf_comm] at h
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr h)

private theorem le_neg_of_inf_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : b ⊓ a = ⊥) :
    a ≤ bᶜ := by
  apply le_of_sub_eq_bot; rwa [compl_compl]

private theorem sub_eq_bot_of_le {α : Type*} [BooleanAlgebra α] {a b : α} (h : a ≤ b) : bᶜ ⊓ a = ⊥ := by
  rw [← inf_eq_of_le h, inf_comm, inf_assoc, inf_compl_eq_bot, inf_bot_eq]









private theorem deduction_simp {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ≤ imp b c ↔ a ⊓ b ≤ c := deduction.symm



-- Aliases without `@[simp]`: mathlib4's `iSup_option`/`iInf_option` already carry `@[simp]`.








































-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version































































/-! ## tactic.interactive section — DEFERRED

  The tactic extensions (bv_intro, bv_cases_at, bv_or_elim_at, specialize_context,
  bv_split, bv_and_intro, bv_imp_elim_at, bv_mp, bv_imp_intro, bv_split_goal,
  bv_or_inr, bv_or_inl, bv_contradiction, tidy_context, bv_exfalso,
  bv_cases_on, bv_exists_intro, bv_specialize_at, bv_to_pi, bv_to_pi') need
  a complete rewrite for Lean 4's macro/elab system.

  These are deferred until downstream files actually need them.
  - Main block: See src/to_mathlib.lean:1252-1684 for the original definitions.
  - Early block also deferred: src/to_mathlib.lean:492-510 contained `congr1` and `rexact`
    tactics. `congr1` is used in roughly 10 downstream Lean 3 proof sites. In Lean 4,
    `congr 1` (with a space) is a built-in tactic, so when porting `fol`, `henkin`,
    `language_extension`, etc., translate `congr1` (no space) to `congr 1` (with space)
    inline rather than re-implementing the tactic.
-/

-- with_h_asms helper definition



end CohenSource_ToMathlib

/- Source module: Definitions.Flypitch4.Bvm -/
section CohenSource_Bvm
set_option autoImplicit false
local notation "ω'" => _root_.bSet.ω'
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm.lean lines 1-700 — Task 10a -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch

/-! ## Namespace Lattice — natural deduction lemmas in BA -/

namespace Lattice

section natded
variable {𝔹 : Type*} [CompleteBooleanAlgebra 𝔹]

-- src/bvm.lean:21


-- src/bvm.lean:25


-- src/bvm.lean:29


-- src/bvm.lean:33


-- src/bvm.lean:37


-- src/bvm.lean:40


-- src/bvm.lean:43


-- src/bvm.lean:46


-- src/bvm.lean:49


-- src/bvm.lean:53


-- src/bvm.lean:57


-- src/bvm.lean:61


-- src/bvm.lean:68


-- src/bvm.lean:72


-- src/bvm.lean:78


-- src/bvm.lean:82


-- src/bvm.lean:88


-- src/bvm.lean:91


-- src/bvm.lean:94


-- src/bvm.lean:97


-- src/bvm.lean:107


-- src/bvm.lean:122


-- src/bvm.lean:124


-- src/bvm.lean:126


-- src/bvm.lean:128 (bv_and.left → bv_and_left)


-- src/bvm.lean:131 (bv_and.right → bv_and_right)


-- src/bvm.lean:134


-- src/bvm.lean:137


-- src/bvm.lean:140


-- src/bvm.lean:143


-- src/bvm.lean:146


-- src/bvm.lean:149


-- src/bvm.lean:152


-- src/bvm.lean:155
private lemma bv_iff_neg {b₁ b₂ : 𝔹} (H : ∀ {Γ : 𝔹}, Γ ≤ b₁ ↔ Γ ≤ b₂) :
    ∀ {Γ : 𝔹}, Γ ≤ b₁ᶜ ↔ Γ ≤ b₂ᶜ := by
  intro Γ
  simp only [← imp_bot]
  have h12 : b₁ ≤ b₂ := (H (Γ := b₁)).mp le_rfl
  have h21 : b₂ ≤ b₁ := (H (Γ := b₂)).mpr le_rfl
  exact ⟨fun h => le_trans h (imp_le_of_left_le (h := h21)),
         fun h => le_trans h (imp_le_of_left_le (h := h12))⟩

end natded
end Lattice

open Lattice

universe u

/-! ## pSet namespace — small additions -/

namespace PSet

-- src/bvm.lean:173-184


end PSet

/-! ## bSet — boolean-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.


namespace bSet

open scoped Flypitch

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]



-- src/bvm.lean:203


-- src/bvm.lean:206


-- src/bvm.lean:208


-- src/bvm.lean:211


-- src/bvm.lean:215


-- src/bvm.lean:218


-- src/bvm.lean:221






-- src/bvm.lean:229


-- src/bvm.lean:232


-- src/bvm.lean:238






-- src/bvm.lean:255






-- src/bvm.lean:269


-- src/bvm.lean:278


-- src/bvm.lean:281




-- src/bvm.lean:286


-- src/bvm.lean:295


-- src/bvm.lean:298


-- src/bvm.lean:302


-- src/bvm.lean:305




-- src/bvm.lean:310


-- src/bvm.lean:313


-- src/bvm.lean:316


-- src/bvm.lean:319


-- src/bvm.lean:322


-- src/bvm.lean:328


-- src/bvm.lean:331


-- src/bvm.lean:334


-- src/bvm.lean:338


-- src/bvm.lean:341


-- src/bvm.lean:354




-- src/bvm.lean:361


-- src/bvm.lean:366


-- src/bvm.lean:381


-- src/bvm.lean:387


-- src/bvm.lean:393


-- src/bvm.lean:396


-- src/bvm.lean:399


-- src/bvm.lean:402


-- src/bvm.lean:406


-- src/bvm.lean:413


-- src/bvm.lean:472


-- src/bvm.lean:476


-- src/bvm.lean:478


-- src/bvm.lean:485


-- src/bvm.lean:493


-- src/bvm.lean:504


-- src/bvm.lean:514


-- src/bvm.lean:518


-- src/bvm.lean:531


-- src/bvm.lean:544


-- src/bvm.lean:549


-- src/bvm.lean:555


-- src/bvm.lean:560


-- src/bvm.lean:563


-- src/bvm.lean:566


-- src/bvm.lean:576


-- src/bvm.lean:587


-- src/bvm.lean:603


-- src/bvm.lean:616


-- src/bvm.lean:626


-- src/bvm.lean:634


-- src/bvm.lean:639


-- src/bvm.lean:642


-- src/bvm.lean:645


-- src/bvm.lean:648


-- src/bvm.lean:651


-- src/bvm.lean:654


-- src/bvm.lean:657


-- src/bvm.lean:660


-- src/bvm.lean:668


-- src/bvm.lean:676


-- src/bvm.lean:684


-- src/bvm.lean:687


-- src/bvm.lean:690


-- src/bvm.lean:693


-- src/bvm.lean:698


-- src/bvm.lean:702 (dropping the meta-tactic autoParam on H and H')


-- src/bvm.lean:712


-- src/bvm.lean:719


-- src/bvm.lean:723


-- src/bvm.lean:727


-- src/bvm.lean:729


-- src/bvm.lean:732


-- src/bvm.lean:742


-- src/bvm.lean:746


-- ============================================================
-- Task 10b: src/bvm.lean lines 750-1400
-- is_definite, empty lemmas, insert1 congr, singletons,
-- mixture, mixing_lemma, smallness, well_ordering,
-- mixing_corollaries, smallness', cores
-- ============================================================

-- src/bvm.lean:817


-- src/bvm.lean:819


-- src/bvm.lean:825


-- src/bvm.lean:828


-- src/bvm.lean:830


-- src/bvm.lean:833


-- src/bvm.lean:839


-- src/bvm.lean:845


-- src/bvm.lean:852


-- src/bvm.lean:842


-- src/bvm.lean:855


/-! ### singleton lemmas -/

-- src/bvm.lean:860


-- src/bvm.lean:863


-- src/bvm.lean:874


-- src/bvm.lean:877


-- src/bvm.lean:879


-- src/bvm.lean:881


-- src/bvm.lean:883


-- src/bvm.lean:885


/-! ### mixture / mixing lemma -/

-- src/bvm.lean:899


-- src/bvm.lean:904


-- src/bvm.lean:908


-- src/bvm.lean:921


-- src/bvm.lean:925


-- src/bvm.lean:933


-- src/bvm.lean:914


-- src/bvm.lean:937 — Mixing Lemma


-- src/bvm.lean:954


-- src/bvm.lean:957


/-! ### smallness -/

section smallness
variable {ϕ : bSet 𝔹 → 𝔹}

-- src/bvm.lean:988


-- src/bvm.lean:992


-- src/bvm.lean:995


-- src/bvm.lean:998


-- src/bvm.lean:1007


/-! ### well_ordering -/

section well_ordering
variable {α : Type*} (r : α → α → Prop) [IsWellOrder α r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1013


-- src/bvm.lean:1015


-- src/bvm.lean:1017


end well_ordering

variable (r : type (@B_small_witness _ _ ϕ) → type (@B_small_witness _ _ ϕ) → Prop)
variable [IsWellOrder _ r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1029


-- src/bvm.lean:1036


-- src/bvm.lean:1045


-- src/bvm.lean:1048


-- src/bvm.lean:1050


-- src/bvm.lean:1053


-- src/bvm.lean:1060


-- src/bvm.lean:1075
-- Note: the Lean 3 `antichain` means pairwise inf = ⊥, which is exactly witness_antichain_index.
-- The Lean 4 IsAntichain (· ≤ ·) is a different (unprovable here) notion, so we state the
-- correct pairwise-disjoint version.


-- src/bvm.lean:1082


-- src/bvm.lean:1085


end smallness

/-! ### maximum principle and AE_convert -/

-- src/bvm.lean:1107


-- src/bvm.lean:1131


-- src/bvm.lean:1134


-- src/bvm.lean:1138


-- src/bvm.lean:1141


-- src/bvm.lean:1155


-- src/bvm.lean:1164


/-! ### mixing corollaries -/

section mixing_corollaries

-- src/bvm.lean:1175-1208
variable (X u₁ u₂ : bSet 𝔹) (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤)

-- src/bvm.lean:1178


-- src/bvm.lean:1192


end mixing_corollaries

/-! ### core_aux_lemma -/

-- src/bvm.lean:1210


-- src/bvm.lean:1229


/-! ### smallness' -/

section smallness'
variable {α : Type u} (ϕ' : bSet 𝔹 → α)

-- src/bvm.lean:1243


end smallness'

/-! ### cores -/

section cores

-- src/bvm.lean:1250


-- src/bvm.lean:1253


-- src/bvm.lean:1256


-- src/bvm.lean:1262


-- src/bvm.lean:1272


-- src/bvm.lean:1282


-- src/bvm.lean:1285


-- src/bvm.lean:1296


-- src/bvm.lean:1299


-- src/bvm.lean:1301


-- src/bvm.lean:1303


-- src/bvm.lean:1306


-- src/bvm.lean:1309


-- src/bvm.lean:1320


-- src/bvm.lean:1331


-- src/bvm.lean:1334


-- src/bvm.lean:1337


-- src/bvm.lean:1376


-- src/bvm.lean:1379


-- src/bvm.lean:1382


-- src/bvm.lean:1384


-- src/bvm.lean:1387


-- src/bvm.lean:1392


-- src/bvm.lean:1397


-- src/bvm.lean:1424
-- (these lemmas have complex `letI` formulations in Lean 3; skipped as auxiliary)


-- src/bvm.lean:1427


-- src/bvm.lean:1430


-- src/bvm.lean:1432


-- src/bvm.lean:1435


-- src/bvm.lean:1438


-- src/bvm.lean:1443


-- src/bvm.lean:1450


-- src/bvm.lean:1459


-- src/bvm.lean:1470


end cores

section check_names

/-! `check` is the canonical embedding of PSet into bSet.
Note that a check-name is not only definite, but recursively definite. -/

-- src/bvm.lean:1479


-- Postfix notation to match Lean 3 `̌ ` postfix notation


-- src/bvm.lean:1484


-- src/bvm.lean:1487


-- src/bvm.lean:1491


-- src/bvm.lean:1494 (this is trivially true in Lean 4)

-- src/bvm.lean:1497


-- src/bvm.lean:1500


-- src/bvm.lean:1503


-- src/bvm.lean:1506


-- src/bvm.lean:1509


-- src/bvm.lean:1512


-- src/bvm.lean:1516


-- src/bvm.lean:1519


-- src/bvm.lean:1521


-- src/bvm.lean:1523


-- src/bvm.lean:1527


-- src/bvm.lean:1530


-- src/bvm.lean:1536


-- src/bvm.lean:1544


-- src/bvm.lean:1556


-- src/bvm.lean:1560


-- src/bvm.lean:1564


-- src/bvm.lean:1573


-- src/bvm.lean:1581


-- src/bvm.lean:1600


-- src/bvm.lean:1609


-- src/bvm.lean:1612


-- src/bvm.lean:1619


-- src/bvm.lean:1625


-- src/bvm.lean:1628


-- src/bvm.lean:1640


-- src/bvm.lean:1650


-- src/bvm.lean:1662


-- src/bvm.lean:1665


-- src/bvm.lean:1671


-- src/bvm.lean:1678


-- src/bvm.lean:1684


-- src/bvm.lean:1691


-- src/bvm.lean:1699


-- src/bvm.lean:1702


-- src/bvm.lean:1713


-- src/bvm.lean:1746


-- src/bvm.lean:1755


-- src/bvm.lean:1762


-- src/bvm.lean:1766


-- src/bvm.lean:1775


-- src/bvm.lean:1787


end check_names

-- src/bvm.lean:1802-1836 — collect definitions (outside section to avoid section var issues)







-- src/bvm.lean:1814


-- src/bvm.lean:1825



-- src/bvm.lean:1844


-- src/bvm.lean:1860


-- src/bvm.lean:1871


-- src/bvm.lean:1888












-- src/bvm.lean:1971


-- src/bvm.lean:1978








-- src/bvm.lean:1993




-- src/bvm.lean:2026 (bSet_axiom_of_powerset' -- stub for downstream usage)
-- TODO: The full statement uses ⨅ (y : x.type) which has elaboration issues in Lean 4.
-- Replacing with equivalent formulation via bv_powerset_spec.
-- lemma bSet_axiom_of_powerset' {Γ : 𝔹} (u : bSet 𝔹) : ... := by sorry

-- src/bvm.lean:2080
-- Auxiliary: bv_powerset unfolds membership






-- src/bvm.lean:2074
-- Note: direct apply le_iInf fails for bSet-indexed iInf with ⇔ involving ⊆ᴮ
-- due to elaboration issue. We use an auxiliary lemma with an explicit u argument.




-- src/bvm.lean:2091


-- src/bvm.lean:2099


-- src/bvm.lean:2102


-- src/bvm.lean:2108






-- src/bvm.lean:2122


-- src/bvm.lean:2132


-- same as mem_subset.mk_iff, but with better ordering of terms on the RHS
-- src/bvm.lean:2137




-- src/bvm.lean:2147


-- src/bvm.lean:2163


-- src/bvm.lean:2169


-- src/bvm.lean:2184


-- src/bvm.lean:2191


-- src/bvm.lean:2199
section infinity
-- ω stands for PSet.omega throughout this section





-- src/bvm.lean:2207














-- src/bvm.lean:2234


















-- src/bvm.lean:2261


-- Helper: PSet-level membership gives check-level membership




-- src/bvm.lean:2270 (one_eq_singleton_zero) -- TODO: singleton notation for bSet
-- lemma one_eq_singleton_zero : Γ ≤ (1 : bSet 𝔹) =ᴮ {(0 : bSet 𝔹)} := by sorry





-- src/bvm.lean:2291


-- example {w : bSet 𝔹} : let ϕ := fun x => ⨅ z, z ∈ᴮ w ⊓ z ⊆ᴮ x ⊓ x ⊆ᴮ z; B_ext ϕ := by simp

end infinity

-- src/bvm.lean:2310








-- src/bvm.lean:2345
-- Auxiliary statement used in regularity_aux (with Γ = ⊤)








-- src/bvm.lean:2375
section zorns_lemma












end zorns_lemma

-- src/bvm.lean:2487
section comprehension
variable (ϕ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) (H_congr : B_ext ϕ)









variable {ϕ} {H_congr}



variable (ϕ) (H_congr)



end comprehension

-- src/bvm.lean:2557










-- src/bvm.lean:2572






end bSet


end CohenSource_Bvm

/- Source module: Definitions.Flypitch4.BvmExtras -/
section CohenSource_BvmExtras
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm_extras.lean lines 1-700 — Task 14a -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

namespace bSet

section extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]





-- src/bvm_extras.lean:24


-- src/bvm_extras.lean:27


-- src/bvm_extras.lean:30


-- src/bvm_extras.lean:33


-- src/bvm_extras.lean:36


-- src/bvm_extras.lean:39


-- src/bvm_extras.lean:42


-- src/bvm_extras.lean:45


-- src/bvm_extras.lean:48


-- src/bvm_extras.lean:56


-- src/bvm_extras.lean:62


-- src/bvm_extras.lean:69


-- src/bvm_extras.lean:78


-- src/bvm_extras.lean:81


-- src/bvm_extras.lean:84




-- src/bvm_extras.lean:88


-- src/bvm_extras.lean:90


-- src/bvm_extras.lean:92


-- src/bvm_extras.lean:94


-- src/bvm_extras.lean:112


-- src/bvm_extras.lean:126


-- src/bvm_extras.lean:132


-- src/bvm_extras.lean:139


-- src/bvm_extras.lean:146


-- src/bvm_extras.lean:150


-- src/bvm_extras.lean:158


-- src/bvm_extras.lean:166


-- src/bvm_extras.lean:179


-- src/bvm_extras.lean:182


-- src/bvm_extras.lean:185


-- src/bvm_extras.lean:204


-- src/bvm_extras.lean:207


-- src/bvm_extras.lean:209


-- src/bvm_extras.lean:216


-- src/bvm_extras.lean:219


-- src/bvm_extras.lean:222


-- src/bvm_extras.lean:225


-- src/bvm_extras.lean:240


-- src/bvm_extras.lean:243


-- src/bvm_extras.lean:246


-- src/bvm_extras.lean:257


-- src/bvm_extras.lean:260


-- src/bvm_extras.lean:263


-- src/bvm_extras.lean:265


-- src/bvm_extras.lean:270


-- src/bvm_extras.lean:273


-- src/bvm_extras.lean:276


-- src/bvm_extras.lean:287


-- src/bvm_extras.lean:297


-- src/bvm_extras.lean:316


-- src/bvm_extras.lean:330


-- src/bvm_extras.lean:333


-- src/bvm_extras.lean:342


-- src/bvm_extras.lean:345


-- src/bvm_extras.lean:349


-- src/bvm_extras.lean:353


-- src/bvm_extras.lean:355


-- src/bvm_extras.lean:357


-- src/bvm_extras.lean:360


-- src/bvm_extras.lean:362


-- src/bvm_extras.lean:366


-- src/bvm_extras.lean:371


-- src/bvm_extras.lean:389


-- src/bvm_extras.lean:392


-- src/bvm_extras.lean:400


-- src/bvm_extras.lean:408


-- src/bvm_extras.lean:411


-- src/bvm_extras.lean:415


-- src/bvm_extras.lean:428


-- src/bvm_extras.lean:441


-- src/bvm_extras.lean:448


-- src/bvm_extras.lean:465


-- src/bvm_extras.lean:489


-- src/bvm_extras.lean:494


-- src/bvm_extras.lean:499


-- src/bvm_extras.lean:506
-- (In Lean 4 port, PSet.pair is PSet.pSet_pair from PSetOrdinal.lean)


-- Auxiliary: propositional equality check (pSet_pair a b) = pair (check a) (check b)


-- src/bvm_extras.lean:514
-- (In Lean 4 port, PSet.prod is PSet.pSet_prod from PSetOrdinal.lean)


-- src/bvm_extras.lean:535


-- src/bvm_extras.lean:538


-- src/bvm_extras.lean:548


-- src/bvm_extras.lean:551


-- src/bvm_extras.lean:561


-- src/bvm_extras.lean:565


-- src/bvm_extras.lean:568
private lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} :
    Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f := by
  -- Prove is_total = is_total' at the value level, then rewrite
  -- bounded_forall converts ⨅ i, x.bval i ⟹ ψ (x.func i) ↔ ⨅ w, w ∈ x ⟹ ψ w
  -- bounded_exists converts ⨆ j, y.bval j ⊓ ϕ (y.func j) ↔ ⨆ w, w ∈ y ⊓ ϕ w
  -- Prove is_total = is_total' using bounded_forall and bounded_exists
  suffices h : is_total x y f = is_total' x y f by rw [h]
  simp only [is_total, is_total']
  -- Step 1: expand inner ⨆ on LHS via bounded_exists
  have inner_eq : ∀ w₁ : bSet 𝔹, (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
      (⨆ j : y.type, y.bval j ⊓ pair w₁ (y.func j) ∈ᴮ f) :=
    fun w₁ => (@bounded_exists 𝔹 _ y (fun w₂ => pair w₁ w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)).symm
  -- Step 2: expand outer ⨅ via bounded_forall
  rw [show (⨅ w₁ : bSet 𝔹, w₁ ∈ᴮ x ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
       (⨅ i : x.type, x.bval i ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair (x.func i) w₂ ∈ᴮ f) from
    (@bounded_forall 𝔹 _ x (fun w₁ => ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)
      (h_congr := fun w₁ w₂ =>
        B_ext_iSup (h := fun w₂ => B_ext_inf B_ext_const B_ext_pair_mem_left) w₁ w₂)).symm]
  congr 1; ext i
  congr 1
  exact inner_eq (x.func i)

-- src/bvm_extras.lean:581




-- src/bvm_extras.lean:588


-- src/bvm_extras.lean:591


-- src/bvm_extras.lean:595


-- src/bvm_extras.lean:604
-- aka function extensionality


-- src/bvm_extras.lean:610
-- aka function extensionality


-- src/bvm_extras.lean:614


-- src/bvm_extras.lean:622
-- bounded image


-- src/bvm_extras.lean:625


-- src/bvm_extras.lean:628


-- src/bvm_extras.lean:638

-- src/bvm_extras.lean:649


-- src/bvm_extras.lean:658


-- src/bvm_extras.lean:668
-- bounded preimage


-- src/bvm_extras.lean:671


-- src/bvm_extras.lean:673




-- src/bvm_extras.lean:687


-- src/bvm_extras.lean:690


-- src/bvm_extras.lean:692


-- src/bvm_extras.lean:694


-- src/bvm_extras.lean:697


-- src/bvm_extras.lean:699


-- ============================================================
-- Task 14b: src/bvm_extras.lean lines 700-1300
-- ============================================================

-- src/bvm_extras.lean:702


-- src/bvm_extras.lean:709


-- src/bvm_extras.lean:716


-- src/bvm_extras.lean:727


-- src/bvm_extras.lean:740


-- src/bvm_extras.lean:757
-- Helper: membership in check f as iSup over indices




-- src/bvm_extras.lean:797


-- src/bvm_extras.lean:800


-- src/bvm_extras.lean:804


-- src/bvm_extras.lean:807


-- src/bvm_extras.lean:810


-- src/bvm_extras.lean:812


-- src/bvm_extras.lean:814


-- src/bvm_extras.lean:821


-- src/bvm_extras.lean:824


-- src/bvm_extras.lean:828


-- src/bvm_extras.lean:868


-- src/bvm_extras.lean:879
-- not really funext since it doesn't use extensionality in an essential way


-- src/bvm_extras.lean:891




-- src/bvm_extras.lean:897


-- src/bvm_extras.lean:900


-- src/bvm_extras.lean:913


-- src/bvm_extras.lean:921


-- src/bvm_extras.lean:931


-- src/bvm_extras.lean:938


-- src/bvm_extras.lean:946


-- src/bvm_extras.lean:950


-- src/bvm_extras.lean:952


-- src/bvm_extras.lean:954


-- src/bvm_extras.lean:963


-- src/bvm_extras.lean:969


-- src/bvm_extras.lean:972


-- src/bvm_extras.lean:981


-- src/bvm_extras.lean:983


-- src/bvm_extras.lean:985
-- larger_than y z = ⨆ S f, S ⊆ y ⊓ is_func' S z f ⊓ is_surj S z f
-- B_ext as function of z:
-- is_total S z f = ⨅ w₁, w₁ ∈ S ⟹ ⨆ w₂, w₂ ∈ z ⊓ pair w₁ w₂ ∈ f
-- is_surj S z f = ⨅ v, v ∈ z ⟹ ⨆ w, w ∈ S ⊓ pair w v ∈ f






-- src/bvm_extras.lean:988
-- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
-- B_ext as function of z: S ⊆ z = ⨅ j, S.bval j ⟹ S.func j ∈ z


-- src/bvm_extras.lean:991
-- injects_into z y = ⨆ f, is_func' z y f ⊓ is_inj f
-- is_func' z y f = is_func f ⊓ is_total z y f
-- is_total z y f = ⨅ w₁, w₁ ∈ z ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
-- B_ext as function of z: w₁ ∈ z changes with z


-- src/bvm_extras.lean:994
-- injects_into y z = ⨆ f, is_func' y z f ⊓ is_inj f
-- B_ext as function of z (in codomain y→z)


-- ============================================================
-- src/bvm_extras.lean lines 1004-1300
-- ============================================================

-- src/bvm_extras.lean:1018
-- The pointed_extension construction: extends a partial surjection f : S ↠ y
-- to a total surjection x ↠ y by mapping elements outside S to b.
-- This definition uses subset.mk over (prod x y).type, with bval encoding
-- the condition.


-- src/bvm_extras.lean:1023


-- src/bvm_extras.lean:1072-1215: All lemmas about pointed_extension
-- These are sorry-stubbed since they require heavy tactic work.

-- src/bvm_extras.lean:1136


-- src/bvm_extras.lean:1177


-- src/bvm_extras.lean:1191


-- src/bvm_extras.lean:1198


-- src/bvm_extras.lean:1209


-- src/bvm_extras.lean:1220


-- src/bvm_extras.lean:1230


-- src/bvm_extras.lean:1238


-- src/bvm_extras.lean:1273


-- src/bvm_extras.lean:1291


-- ============================================================
-- src/bvm_extras.lean lines 1300-1900
-- ============================================================

-- src/bvm_extras.lean:1301
-- Given a surjection f : x ↠ z and an injection g : y ↪ z, lift f along g to a surjection f' : x ↠ y.


-- src/bvm_extras.lean:1306
private lemma ex_witness_of_mem_lift_surj_inj {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (_H_is_func'_f : Γ ≤ is_func' x z f)
    (H : Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj)) :
    Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  unfold lift_surj_inj at H
  rw [mem_subset.mk_iff] at H
  apply H.trans
  apply iSup_le; intro pr; obtain ⟨i, j⟩ := pr
  simp only [prod_func, prod_bval]
  -- Context: pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
  --           (⨆ w, w ∈ z ⊓ pair (x.func i) w ∈ f ⊓ pair (y.func j) w ∈ g) ⊓ (x.bval i ⊓ y.bval j)
  -- Extract: w₁ =ᴮ x.func i (eq_of_eq_pair_left) and w₂ =ᴮ y.func j (eq_of_eq_pair_right)
  -- After simp, goal is (A ⊓ B) ⊓ C ≤ ⨆ w, ...
  -- where A = pair w₁ w₂ =ᴮ pair (x.func i) (y.func j), B = ⨆ w..., C = bval
  -- Use `le_trans inf_le_left X` for dropping C, then `le_trans inf_le_left/right` for A or B
  -- After simp, goal is: A ⊓ (B ⊓ C) ≤ ⨆ w, w ∈ z ⊓ pair w₁ w ∈ f ⊓ pair w₂ w ∈ g
  -- where A = pair w₁ w₂ =ᴮ pair xi yj, B = ⨆ w (inner), C = x.bval i ⊓ y.bval j
  have hw1 : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ w₁ =ᴮ x.func i :=
    inf_le_left.trans eq_of_eq_pair_left
  have hw2 : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ w₂ =ᴮ y.func j :=
    inf_le_left.trans eq_of_eq_pair_right
  have hsupr : pair w₁ w₂ =ᴮ pair (x.func i) (y.func j) ⊓
      ((⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g) ⊓ (x.bval i ⊓ y.bval j))
      ≤ ⨆ w, w ∈ᴮ z ⊓ pair (x.func i) w ∈ᴮ f ⊓ pair (y.func j) w ∈ᴮ g :=
    inf_le_right.trans inf_le_left
  -- Carry context then substitute
  -- Goal: A ⊓ (B ⊓ C) ≤ ⨆ w, w ∈ z ⊓ pair w₁ w ∈ f ⊓ pair w₂ w ∈ g
  -- where A = pair w₁ w₂ =ᴮ pair xi yj, B = ⨆ w (inner), C = x.bval i ⊓ y.bval j
  apply (le_inf hsupr le_rfl).trans
  apply (iSup_inf_eq _ _).le.trans
  apply iSup_le; intro w
  apply le_iSup_of_le w
  -- Goal: (inner_w ∈ z ⊓ pair xi w ∈ f ⊓ pair yj w ∈ g) ⊓ (A ⊓ (B ⊓ C)) ≤ w ∈ z ⊓ pair w₁ w ∈ f ⊓ pair w₂ w ∈ g
  refine le_inf (le_inf ?_ ?_) ?_
  · -- w ∈ z: via (inner_w ∈ z ⊓ ...) ⊓ ... ≤ inner_w ∈ z ⊓ ... ≤ w ∈ z ⊓ ... ≤ w ∈ z
    exact inf_le_left.trans (inf_le_left.trans inf_le_left)
  · -- pair w₁ w ∈ f: inner D = ((w ∈ z) ⊓ pair xi w ∈ f) ⊓ pair yj w ∈ g
    -- pair xi w ∈ f: inf_le_left.trans inf_le_right on D, then inf_le_left on D ⊓ F
    exact bv_rw' (H := inf_le_right.trans hw1) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans (inf_le_left.trans inf_le_right))
  · -- pair w₂ w ∈ g: pair yj w ∈ g = inf_le_right on D, then inf_le_left on D ⊓ F
    exact bv_rw' (H := inf_le_right.trans hw2) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans inf_le_right)

-- src/bvm_extras.lean:1318
private lemma mem_lift_surj_inj_iff {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func'_f : Γ ≤ is_func' x z f) {H_mem₁ : Γ ≤ w₁ ∈ᴮ x} {H_mem₂ : Γ ≤ w₂ ∈ᴮ y} :
    Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj) ↔
      Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  constructor
  · exact ex_witness_of_mem_lift_surj_inj H_is_func'_f
  · intro H_ex
    -- Use subst_congr_mem_left' to reduce to pair (x.func i) (y.func j) membership
    rw [mem_unfold] at H_mem₁ H_mem₂
    -- Extract i, j using carry-context pattern
    apply le_trans (le_inf (le_inf H_ex H_mem₁) H_mem₂)
    rw [inf_iSup_eq']; apply iSup_le; intro j
    rw [inf_iSup_eq', iSup_inf_eq']; apply iSup_le; intro i
    rw [iSup_inf_eq', iSup_inf_eq']; apply iSup_le; intro w
    -- Now: (D_w ⊓ E_i) ⊓ F_j ≤ pair w₁ w₂ ∈ lift_surj_inj
    -- Strategy: show pair (x.func i) (y.func j) ∈ lift_surj_inj first, then use subst_congr_mem_left'
    have hw1xi : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤ w₁ =ᴮ x.func i :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hw2yj : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤ w₂ =ᴮ y.func j :=
      inf_le_right.trans inf_le_right
    -- Prove pair (x.func i) (y.func j) ∈ lift_surj_inj first, then use subst_congr
    have hmem_ij : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
        (y.bval j ⊓ w₂ =ᴮ y.func j) ≤
        pair (x.func i) (y.func j) ∈ᴮ lift_surj_inj y H_surj H_inj := by
      unfold lift_surj_inj; rw [mem_subset.mk_iff]
      apply le_iSup_of_le (i, j)
      -- Goal: ctx ≤ pair (x.func i) (y.func j) =ᴮ (prod x y).func (i,j) ⊓ (φ(i,j) ⊓ bvals)
      -- Here pair xi yj =ᴮ pair xi yj = ⊤
      -- Use simp to evaluate bv_eq
      simp only [bv_eq_refl, prod_func, prod_bval, top_inf_eq]
      -- After simp: pair xi yj =ᴮ pair xi yj = ⊤, so the first component vanishes
      -- ctx = (D_w ⊓ E_i) ⊓ F_j where D_w = ((w∈z ⊓ pair w₁ w ∈ f) ⊓ pair w₂ w ∈ g)
      -- E_i = x.bval i ⊓ w₁ =ᴮ x.func i, F_j = y.bval j ⊓ w₂ =ᴮ y.func j
      have hDw : (w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g ⊓ (x.bval i ⊓ w₁ =ᴮ x.func i)) ⊓
          (y.bval j ⊓ w₂ =ᴮ y.func j) ≤
          w ∈ᴮ z ⊓ pair w₁ w ∈ᴮ f ⊓ pair w₂ w ∈ᴮ g := inf_le_left.trans inf_le_left
      refine le_inf ?_ ?_
      · apply bv_use w
        refine le_inf (le_inf ?_ ?_) ?_
        · exact hDw.trans (inf_le_left.trans inf_le_left)
        · exact bv_rw' (H := bv_symm hw1xi) (h_congr := B_ext_pair_mem_left)
            (H_new := hDw.trans (inf_le_left.trans inf_le_right))
        · exact bv_rw' (H := bv_symm hw2yj) (h_congr := B_ext_pair_mem_left)
            (H_new := hDw.trans inf_le_right)
      · exact le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_left)
    -- Now use subst_congr_mem_left' to convert from pair xi yj to pair w₁ w₂
    exact subst_congr_mem_left' (bv_symm (pair_congr hw1xi hw2yj)) hmem_ij

-- src/bvm_extras.lean:1346
private lemma lift_surj_inj_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func_f : Γ ≤ is_func' x z f) :
    Γ ≤ is_func (lift_surj_inj y H_surj H_inj) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]
  -- ctx = ((Γ ⊓ (mem₁ ⊓ mem₂)) ⊓ w₁ = w₂)
  -- Use exists_convert to extract witnesses c₁ and c₂ classically from the full ctx
  have H_gr₁ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ c₁, (c₁ ∈ᴮ z ⊓ pair w₁ c₁ ∈ᴮ f ⊓ pair v₁ c₁ ∈ᴮ g) :=
    inf_le_left.trans (@ex_witness_of_mem_lift_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj))
      w₁ v₁ (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      (le_trans inf_le_left H_is_func_f) (inf_le_right.trans inf_le_left))
  have H_gr₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤
      ⨆ c₂, (c₂ ∈ᴮ z ⊓ pair w₂ c₂ ∈ᴮ f ⊓ pair v₂ c₂ ∈ᴮ g) :=
    inf_le_left.trans (@ex_witness_of_mem_lift_surj_inj 𝔹 _ x y z f g
      (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
             pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj))
      w₂ v₂ (le_trans inf_le_left H_surj) (le_trans inf_le_left H_inj)
      (le_trans inf_le_left H_is_func_f) (inf_le_right.trans inf_le_right))
  -- Extract witnesses c₁, c₂ classically
  obtain ⟨c₁, Hc₁⟩ := exists_convert H_gr₁
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_right) B_ext_pair_mem_right)
  obtain ⟨c₂, Hc₂⟩ := exists_convert H_gr₂
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_right) B_ext_pair_mem_right)
  -- Hc₁ : ctx ≤ c₁ ∈ z ⊓ pair w₁ c₁ ∈ f ⊓ pair v₁ c₁ ∈ g
  -- Hc₂ : ctx ≤ c₂ ∈ z ⊓ pair w₂ c₂ ∈ f ⊓ pair v₂ c₂ ∈ g
  have hw₁c₁_f : _ ≤ pair w₁ c₁ ∈ᴮ f := Hc₁.trans (inf_le_left.trans inf_le_right)
  have hw₂c₂_f : _ ≤ pair w₂ c₂ ∈ᴮ f := Hc₂.trans (inf_le_left.trans inf_le_right)
  have hv₁c₁_g : _ ≤ pair v₁ c₁ ∈ᴮ g := Hc₁.trans inf_le_right
  have hv₂c₂_g : _ ≤ pair v₂ c₂ ∈ᴮ g := Hc₂.trans inf_le_right
  have hw₁w₂ : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right
  -- Prove c₁ = c₂ via is_func' f (using that ctx ≤ Γ ≤ is_func' x z f)
  have hfunc' : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ is_func' x z f :=
    inf_le_left.trans (inf_le_left.trans H_is_func_f)
  have hinj : (Γ ⊓ (pair w₁ v₁ ∈ᴮ lift_surj_inj y H_surj H_inj ⊓
      pair w₂ v₂ ∈ᴮ lift_surj_inj y H_surj H_inj)) ⊓ w₁ =ᴮ w₂ ≤ is_inj g :=
    inf_le_left.trans (inf_le_left.trans H_inj)
  have hc₁c₂ := eq_of_is_func'_of_eq hfunc' hw₁w₂ hw₁c₁_f hw₂c₂_f
  exact eq_of_is_inj_of_eq hinj hc₁c₂ hv₁c₁_g hv₂c₂_g

-- src/bvm_extras.lean:1362
private lemma lift_surj_inj_is_total {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g) (H_is_func_f : Γ ≤ is_func' S z f) :
    Γ ≤ is_total (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  unfold is_total
  apply le_iInf; intro w₁; rw [← deduction]
  -- ctx₀ = Γ ⊓ (w₁ ∈ subset.mk φ)
  -- Use carry-context to extract i (S.type), b (bSet), j (y.type)
  apply le_trans (le_inf (mem_subset.mk_iff.mp inf_le_right) le_rfl)
  -- Goal: (⨆ i : S.type, w₁ =ᴮ S.func i ⊓ (φ i ⊓ S.bval i)) ⊓ ctx₀ ≤ ⨆ b, b ∈ y ⊓ pair w₁ b ∈ lift_surj_inj
  rw [iSup_inf_eq']; apply iSup_le; intro i
  -- ctx_i = (w₁ =ᴮ S.func i ⊓ (φ i ⊓ S.bval i)) ⊓ ctx₀
  -- Extract b from φ i = ⨆ b, b ∈ y ⊓ ⨆ c, c ∈ z ⊓ pair (S.func i) c ∈ f ⊓ pair b c ∈ g
  apply le_trans (le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) le_rfl)
  -- (⨆ b, b ∈ y ⊓ ...) ⊓ ctx_i
  rw [iSup_inf_eq']; apply iSup_le; intro b
  -- ctx_b = (b ∈ y ⊓ ⨆ c, ...) ⊓ ctx_i
  apply le_iSup_of_le b
  refine le_inf (inf_le_left.trans inf_le_left) ?_
  -- pair w₁ b ∈ lift_surj_inj: extract j from b ∈ y via carry-context
  -- b ∈ y as iSup: need to distribute it
  have H_b_mem_y : (b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g) ⊓
      ((w₁ =ᴮ S.func i ⊓ ((⨆ b', b' ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓
        pair b' c ∈ᴮ g) ⊓ S.bval i)) ⊓
        (Γ ⊓ w₁ ∈ᴮ subset.mk (fun i : S.type =>
          ⨆ b', b' ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b' c ∈ᴮ g))) ≤
      ⨆ j : y.type, y.bval j ⊓ b =ᴮ y.func j := by
    rw [← mem_unfold]; exact inf_le_left.trans inf_le_left
  apply le_trans (le_inf H_b_mem_y le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro j
  -- ctx_j = (y.bval j ⊓ b =ᴮ y.func j) ⊓ ctx_b
  -- Prove pair w₁ b ∈ lift_surj_inj using subst_congr_mem_left'
  -- First prove pair (S.func i) (y.func j) ∈ lift_surj_inj (with bv_eq_refl), then convert
  apply subst_congr_mem_left' (bv_symm (pair_congr
    (show _ ≤ w₁ =ᴮ S.func i from inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    (show _ ≤ b =ᴮ y.func j from inf_le_left.trans inf_le_right)))
  -- Prove pair (S.func i) (y.func j) ∈ lift_surj_inj
  unfold lift_surj_inj; rw [mem_subset.mk_iff]
  apply le_iSup_of_le (i, j)
  simp only [bv_eq_refl, prod_func, prod_bval, top_inf_eq]
  -- ctx_j ≤ (⨆ c, c ∈ z ⊓ pair (S.func i) c ∈ f ⊓ pair (y.func j) c ∈ g) ⊓ (S.bval i ⊓ y.bval j)
  refine le_inf ?_ (le_inf ?_ ?_)
  · -- ⨆ c, c ∈ z ⊓ pair (S.func i) c ∈ f ⊓ pair (y.func j) c ∈ g
    apply le_trans (le_inf (inf_le_right.trans (inf_le_left.trans inf_le_right)) le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro c
    apply le_iSup_of_le c
    refine le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))) ?_
    -- pair (y.func j) c ∈ g from pair b c ∈ g and b =ᴮ y.func j
    -- pair b c ∈ g: ctx_c ≤ A ≤ pair b c ∈ g = inf_le_left.trans inf_le_right
    -- b =ᴮ y.func j: from ctx_j → inf_le_left.trans inf_le_right, ctx_c → ctx_j via inf_le_right
    exact bv_rw' (H := bv_symm (inf_le_right.trans (inf_le_left.trans inf_le_right)))
      (ϕ := fun w => pair w c ∈ᴮ g) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_left.trans inf_le_right)
  · -- S.bval i: ctx_j → ctx_b → ctx_i → (w₁ =ᴮ S.func i ⊓ (...⊓ S.bval i)) → ...⊓ S.bval i → S.bval i
    exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
  · -- y.bval j: ctx_j → y.bval j ⊓ b =ᴮ y.func j → y.bval j
    exact inf_le_left.trans inf_le_left

-- src/bvm_extras.lean:1375
private lemma lift_surj_inj_is_surj {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g)
    (H_is_func_f : Γ ≤ is_func' S z f) (H_is_func_g : Γ ≤ is_func' y z g) :
    Γ ≤ is_surj (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  unfold is_surj
  apply le_iInf; intro b; rw [← deduction]
  -- ctx₀ = Γ ⊓ b ∈ y
  -- Goal: ctx₀ ≤ ⨆ v, v ∈ subset.mk φ ⊓ pair v b ∈ lift_surj_inj y H_surj H_inj
  -- Step 1: get w₂ ∈ z ⊓ pair b w₂ ∈ g via is_total g
  have H_tot_g : Γ ⊓ b ∈ᴮ y ≤ ⨆ w₂, w₂ ∈ᴮ z ⊓ pair b w₂ ∈ᴮ g :=
    le_trans (le_inf (inf_le_left.trans (le_trans (is_total_of_is_func' H_is_func_g)
      (iInf_le _ b))) inf_le_right) bv_imp_elim
  obtain ⟨w₂, Hw₂⟩ := exists_convert H_tot_g
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  -- Hw₂ : ctx₀ ≤ w₂ ∈ z ⊓ pair b w₂ ∈ g
  -- Step 2: get v ∈ S ⊓ pair v w₂ ∈ f via H_surj applied at w₂
  have H_surj_w₂ : Γ ⊓ b ∈ᴮ y ≤ ⨆ v, v ∈ᴮ S ⊓ pair v w₂ ∈ᴮ f :=
    le_trans (le_inf (inf_le_left.trans (le_trans H_surj (iInf_le _ w₂)))
      (Hw₂.trans inf_le_left)) bv_imp_elim
  obtain ⟨v, Hv⟩ := exists_convert H_surj_w₂
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  -- Hv : ctx₀ ≤ v ∈ S ⊓ pair v w₂ ∈ f
  -- Provide v as the output
  apply le_iSup_of_le v
  refine le_inf ?_ ?_
  · -- v ∈ subset.mk φ: expand v ∈ S to ⨆ i, S.bval i ⊓ v =ᴮ S.func i, extract i
    have Hv_mem_S : Γ ⊓ b ∈ᴮ y ≤ ⨆ i : S.type, S.bval i ⊓ v =ᴮ S.func i := by
      rw [← mem_unfold]; exact Hv.trans inf_le_left
    -- Use carry-context to extract i
    apply le_trans (le_inf Hv_mem_S le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro i
    -- ctx_i = (S.bval i ⊓ v =ᴮ S.func i) ⊓ ctx₀
    rw [mem_subset.mk_iff]
    apply le_iSup_of_le i
    -- Goal: ctx_i ≤ v =ᴮ S.func i ⊓ (φ i ⊓ S.bval i)
    -- where φ i = ⨆ b', b' ∈ y ⊓ ⨆ c, c ∈ z ⊓ pair (S.func i) c ∈ f ⊓ pair b' c ∈ g
    refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))
    -- φ i: use bv_use b, then bv_use w₂
    apply le_iSup_of_le b
    refine le_inf (inf_le_right.trans inf_le_right) ?_
    apply le_iSup_of_le w₂
    refine le_inf (le_inf (inf_le_right.trans (Hw₂.trans inf_le_left)) ?_)
      (inf_le_right.trans (Hw₂.trans inf_le_right))
    -- pair (S.func i) w₂ ∈ f: from pair v w₂ ∈ f and v =ᴮ S.func i
    -- v =ᴮ S.func i: from (S.bval i ⊓ v =ᴮ S.func i) = inf_le_left.trans inf_le_right
    exact bv_rw' (H := bv_symm (inf_le_left.trans inf_le_right))
      (ϕ := fun w => pair w w₂ ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
      (H_new := inf_le_right.trans (Hv.trans inf_le_right))
  · -- pair v b ∈ lift_surj_inj y H_surj H_inj
    -- Use mem_lift_surj_inj_iff.mpr with witness w₂
    apply (mem_lift_surj_inj_iff (H_surj := le_trans inf_le_left H_surj)
        (H_inj := le_trans inf_le_left H_inj)
        (H_is_func'_f := le_trans inf_le_left H_is_func_f)
        (H_mem₁ := Hv.trans inf_le_left)
        (H_mem₂ := inf_le_right)).mpr
    apply le_iSup_of_le w₂
    exact le_inf (le_inf (Hw₂.trans inf_le_left) (Hv.trans inf_le_right))
      (Hw₂.trans inf_le_right)

-- src/bvm_extras.lean:1404


-- src/bvm_extras.lean:1410


-- src/bvm_extras.lean:1422


-- src/bvm_extras.lean:1445


-- src/bvm_extras.lean:1457


-- src/bvm_extras.lean:1472


-- src/bvm_extras.lean:1486
-- (locally: ≺ means (larger_than x y)ᶜ, ≼ means injects_into x y)
private lemma bSet_lt_of_lt_of_le {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ (larger_than x y)ᶜ) (H₂ : Γ ≤ injects_into y z) :
    Γ ≤ (larger_than x z)ᶜ := by
  -- Convert ᶜ to implication: Γ ≤ aᶜ ↔ Γ ⊓ a ≤ ⊥
  simp only [← imp_bot]; rw [← deduction]
  -- Goal: Γ ⊓ larger_than x z ≤ ⊥
  -- H₁ : Γ ≤ (larger_than x y)ᶜ, convert to: Γ ⊓ larger_than x y ≤ ⊥
  have H₁' : Γ ⊓ larger_than x y ≤ ⊥ := by
    simp only [← imp_bot] at H₁; rwa [← deduction] at H₁
  -- Strategy: Γ ⊓ larger_than x z ≤ Γ ⊓ larger_than x y (lift surjection along injection)
  apply le_trans _ H₁'
  apply le_inf inf_le_left
  -- Goal: Γ ⊓ larger_than x z ≤ larger_than x y
  simp only [larger_than, injects_into] at *
  -- Goal: Γ ⊓ (⨆ S, ⨆ f, S ⊆ x ⊓ is_func' S z f ⊓ is_surj S z f) ≤ ⨆ S', ⨆ f', S' ⊆ x ⊓ is_func' S' y f' ⊓ is_surj S' y f'
  -- H₂ : Γ ≤ ⨆ g, is_func' y z g ⊓ is_inj g
  -- combine
  apply le_trans (le_inf inf_le_right (inf_le_left.trans H₂))
  -- (⨆ S, ⨆ f, ...) ⊓ (⨆ g, is_func' y z g ⊓ is_inj g) ≤ ⨆ S', ⨆ f', ...
  rw [iSup_inf_eq']; simp_rw [inf_iSup_eq']; apply iSup_le; intro S; apply iSup_le; intro g
  simp_rw [iSup_inf_eq']; apply iSup_le; intro f
  -- ctx = ((S ⊆ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓ (is_func' y z g ⊓ is_inj g))
  have H_func_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_func' S z f :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have H_surj_f : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_surj S z f :=
    inf_le_left.trans inf_le_right
  have H_sub_x : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ S ⊆ᴮ x :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have H_inj_g : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_inj g :=
    inf_le_right.trans inf_le_right
  have H_func_g : (S ⊆ᴮ x ⊓ is_func' S z f ⊓ is_surj S z f) ⊓
      (is_func' y z g ⊓ is_inj g) ≤ is_func' y z g :=
    inf_le_right.trans inf_le_left
  apply le_iSup_of_le (subset.mk (fun i : S.type =>
    ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g))
  apply le_iSup_of_le (lift_surj_inj y H_surj_f H_inj_g)
  refine le_inf (le_inf (subset_trans' subset.mk_subset H_sub_x) (le_inf ?_ ?_)) ?_
  · exact lift_surj_inj_is_func H_func_f
  · exact lift_surj_inj_is_total H_surj_f H_inj_g H_func_f
  · exact lift_surj_inj_is_surj H_surj_f H_inj_g H_func_f H_func_g

-- src/bvm_extras.lean:1500


-- ============================================================
-- src/bvm_extras.lean:1513-1604: is_func'_comp section
-- ============================================================

-- src/bvm_extras.lean:1518


-- src/bvm_extras.lean:1521


-- src/bvm_extras.lean:1554


-- src/bvm_extras.lean:1565


-- src/bvm_extras.lean:1576


-- src/bvm_extras.lean:1583


-- src/bvm_extras.lean:1594


-- src/bvm_extras.lean:1606


-- src/bvm_extras.lean:1609


-- src/bvm_extras.lean:1616


-- src/bvm_extras.lean:1619


-- src/bvm_extras.lean:1625


-- src/bvm_extras.lean:1628


-- src/bvm_extras.lean:1636


-- src/bvm_extras.lean:1639


-- src/bvm_extras.lean:1653


-- src/bvm_extras.lean:1692


-- src/bvm_extras.lean:1700


-- src/bvm_extras.lean:1703


-- src/bvm_extras.lean:1705


-- src/bvm_extras.lean:1707


-- src/bvm_extras.lean:1709


-- ============================================================
-- src/bvm_extras.lean:1732-1798: function_mk' section
-- ============================================================

-- src/bvm_extras.lean:1740


-- src/bvm_extras.lean:1757


-- src/bvm_extras.lean:1767


-- src/bvm_extras.lean:1774


-- src/bvm_extras.lean:1780


-- src/bvm_extras.lean:1788


-- ============================================================
-- src/bvm_extras.lean:1800-1888: inj_inverse section
-- ============================================================

-- src/bvm_extras.lean:1806


-- src/bvm_extras.lean:1809


-- src/bvm_extras.lean:1841


-- src/bvm_extras.lean:1850


-- src/bvm_extras.lean:1858


-- src/bvm_extras.lean:1865


-- src/bvm_extras.lean:1875


-- src/bvm_extras.lean:1877


-- src/bvm_extras.lean:1880


-- ============================================================
-- src/bvm_extras.lean:1890-1900: injective_function_inverse section
-- ============================================================

section injective_function_inverse_section
variable {Γ : 𝔹}

-- src/bvm_extras.lean:1892


-- src/bvm_extras.lean:1895


-- src/bvm_extras.lean:1898


end injective_function_inverse_section

-- ============================================================
-- src/bvm_extras.lean:1902-1927: function_eval section
-- ============================================================

-- Helper: get existential from is_total


-- src/bvm_extras.lean:1906


-- src/bvm_extras.lean:1914


-- src/bvm_extras.lean:1921


-- src/bvm_extras.lean:1924


-- ============================================================
-- src/bvm_extras.lean:1930: surjects_onto_of_injects_into
-- ============================================================

-- src/bvm_extras.lean:1930


-- ============================================================
-- src/bvm_extras.lean:1956-1989: functionMk (= function.mk) and check''
-- ============================================================

-- src/bvm_extras.lean:1956: function.mk renamed to functionMk
-- (functionMk' already exists; this is a different construction called function.mk in Lean 3)










-- src/bvm_extras.lean:1972: check' named check'' to avoid collision






-- src/bvm_extras.lean:1978
private lemma functionMk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := by
  -- is_func g = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ g ⊓ pair w₂ v₂ ∈ g ⊓ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, top_inf_eq]
  -- Goal: pair w₁ v₁ ∈ functionMk ⊓ pair w₂ v₂ ∈ functionMk ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  -- Extract i from pair w₁ v₁ ∈ functionMk
  have hmem_left : pair w₁ v₁ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ i : u.type, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  have hmem_right : pair w₂ v₂ ∈ᴮ (functionMk F h_congr : bSet 𝔹) ≤
      ⨆ j : u.type, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j) := by
    simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
  -- Carry context through double iSup
  calc pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)
      ≤ (⨆ i, u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        le_inf (inf_le_left.trans hmem_left) le_rfl
    _ ≤ ⨆ i, (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
          (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)) :=
        (iSup_inf_eq _ _).le
    _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
        apply iSup_le; intro i
        calc (u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
              (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))
            ≤ (⨆ j, u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              le_inf (inf_le_right.trans (inf_le_right.trans hmem_right)) le_rfl
          _ ≤ ⨆ j, (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                  (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) :=
              (iSup_inf_eq _ _).le
          _ ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂ := by
              apply iSup_le; intro j
              -- Context: (u.bval j ⊓ w₂v₂=pair(Func j)(F j)) ⊓ (u.bval i ⊓ w₁v₁=pair(Func i)(F i)) ⊓ ...
              have hw1 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₁ v₁ =ᴮ pair (u.func i) (F i) :=
                inf_le_right.trans (inf_le_left.trans inf_le_right)
              have hw2 : (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr))) ≤
                    pair w₂ v₂ =ᴮ pair (u.func j) (F j) :=
                inf_le_left.trans inf_le_right
              rw [← deduction]
              -- Goal: ctx ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ v₂
              -- w₁ =ᴮ u.func i (from hw1: pair_eq_pair_left)
              -- w₂ =ᴮ u.func j (from hw2: pair_eq_pair_left)
              -- v₁ =ᴮ F i (from hw1: pair_eq_pair_right)
              -- v₂ =ᴮ F j (from hw2: pair_eq_pair_right)
              -- F i =ᴮ F j from h_congr (since w₁ =ᴮ w₂ = u.func i =ᴮ u.func j via bv_trans)
              set ctx4 := (u.bval j ⊓ pair w₂ v₂ =ᴮ pair (u.func j) (F j)) ⊓
                    ((u.bval i ⊓ pair w₁ v₁ =ᴮ pair (u.func i) (F i)) ⊓
                      (pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ⊓ pair w₂ v₂ ∈ᴮ (functionMk F h_congr)))
              -- v₁ =ᴮ F i
              have hv1_Fi : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₁ =ᴮ F i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_right)
              -- v₂ =ᴮ F j
              have hv2_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ v₂ =ᴮ F j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_right)
              -- w₁ =ᴮ u.func i
              have hw1_ui : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ u.func i :=
                le_trans inf_le_left (le_trans hw1 eq_of_eq_pair_left)
              -- w₂ =ᴮ u.func j
              have hw2_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₂ =ᴮ u.func j :=
                le_trans inf_le_left (le_trans hw2 eq_of_eq_pair_left)
              -- w₁ =ᴮ w₂
              have hw12 : ctx4 ⊓ w₁ =ᴮ w₂ ≤ w₁ =ᴮ w₂ := inf_le_right
              -- u.func i =ᴮ u.func j via: u.func i =ᴮ w₁ =ᴮ w₂ =ᴮ u.func j
              have h_ui_uj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ u.func i =ᴮ u.func j :=
                bv_trans (bv_symm hw1_ui) (bv_trans hw12 hw2_uj)
              -- F i =ᴮ F j
              have h_Fi_Fj : ctx4 ⊓ w₁ =ᴮ w₂ ≤ F i =ᴮ F j :=
                le_trans h_ui_uj (h_congr i j)
              -- v₁ =ᴮ v₂ via v₁ =ᴮ F i =ᴮ F j =ᴮ v₂ (symm)
              exact bv_trans hv1_Fi (bv_trans h_Fi_Fj (bv_symm hv2_Fj))

-- src/bvm_extras.lean:2041


-- ============================================================
-- src/bvm_extras.lean:2080-2136: bot_of_mem_self, bot_of_mem_mem
-- ============================================================

-- src/bvm_extras.lean:2080


-- src/bvm_extras.lean:2093


-- src/bvm_extras.lean:2099


-- src/bvm_extras.lean:2110


-- src/bvm_extras.lean:2131


end extras

-- ============================================================
-- src/bvm_extras.lean:2140-2218: section check (inside bSet namespace)
-- ============================================================

section bSet_check_extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2154


-- src/bvm_extras.lean:2193


-- src/bvm_extras.lean:2203


-- src/bvm_extras.lean:2206


-- src/bvm_extras.lean:2209


-- src/bvm_extras.lean:2215


end bSet_check_extras

-- ============================================================
-- src/bvm_extras.lean:2220-2396: section powerset (inside bSet namespace)
-- ============================================================

section powerset_section
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable (x : bSet 𝔹)

-- src/bvm_extras.lean:2228
-- powerset_injects_F: maps (bv_powerset x).type → (functions x 𝟚).type
-- encodes χ ↦ characteristic function as subset of x × 𝟚


-- src/bvm_extras.lean:2231


-- Helper: under context Γ, if H_ba : χ_b ⊆ χ_a, then compl_a ⊆ compl_b (pointwise under Γ)


-- src/bvm_extras.lean:2249


-- src/bvm_extras.lean:2301


-- src/bvm_extras.lean:2318


-- src/bvm_extras.lean:2377


-- src/bvm_extras.lean:2387


-- src/bvm_extras.lean:2389


end powerset_section

-- ============================================================
-- src/bvm_extras.lean:2212: check_succ_eq_succ_check (needed by omega_is_omega)
-- ============================================================

-- src/bvm_extras.lean:2212


-- ============================================================
-- src/bvm_extras.lean:2398-2747: section ordinals
-- ============================================================

section ordinals
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2401


-- src/bvm_extras.lean:2403


-- src/bvm_extras.lean:2405


-- src/bvm_extras.lean:2408


-- src/bvm_extras.lean:2410


-- src/bvm_extras.lean:2413


-- src/bvm_extras.lean:2420


-- src/bvm_extras.lean:2422


-- src/bvm_extras.lean:2425


-- src/bvm_extras.lean:2428


-- src/bvm_extras.lean:2430


-- src/bvm_extras.lean:2438
private lemma injects_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ injects_into x y := by
  -- Use functionMk with identity on x.func: sends x.func i to x.func i
  -- The "function" is {pair (x.func i) (x.func i) | i : x.type, x.bval i}
  -- This is functionMk (fun i => x.func i) (fun i j h => h)
  -- To show is_total x y: for x.bval i, x.func i ∈ y from H: x ⊆ y
  -- To show is_inj: from pair w₁ v₁, pair w₂ v₂ in functionMk with v₁ =ᴮ v₂:
  --   v₁ =ᴮ x.func i, v₂ =ᴮ x.func j → x.func i =ᴮ x.func j
  --   w₁ =ᴮ x.func i, w₂ =ᴮ x.func j → w₁ =ᴮ w₂
  -- Use functionMk_is_func and subset to get is_total
  -- For is_total: each x.bval i means x.func i ∈ y (from H)
  rw [subset_unfold] at H
  -- Now H : Γ ≤ ⨅ i, x.bval i ⟹ x.func i ∈ y
  -- Use functionMk (fun i => x.func i) with identity congr
  set F : x.type → bSet 𝔹 := fun i => x.func i
  have h_congr : ∀ i j, x.func i =ᴮ x.func j ≤ F i =ᴮ F j := fun i j => le_refl _
  -- functionMk F h_congr = {pair (x.func i) (x.func i) | i}
  have h_func : (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := functionMk_is_func F h_congr
  -- is_total x y functionMk: for each i with x.bval i, x.func i ∈ y
  have h_total : Γ ≤ is_total x y (functionMk F h_congr) := by
    rw [is_total_iff_is_total']; unfold is_total'
    apply le_iInf; intro i; rw [← deduction]
    -- Goal: Γ ⊓ x.bval i ≤ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ functionMk F h_congr
    -- From H: x.func i ∈ y = ⨆ j, y.bval j ⊓ x.func i =ᴮ y.func j
    have hxi_y : Γ ⊓ x.bval i ≤ x.func i ∈ᴮ y :=
      le_trans (le_inf (le_trans inf_le_left H |>.trans (iInf_le _ i)) inf_le_right) bv_imp_elim
    rw [mem_unfold] at hxi_y
    -- hxi_y : Γ ⊓ x.bval i ≤ ⨆ j, y.bval j ⊓ x.func i =ᴮ y.func j
    calc Γ ⊓ x.bval i
        ≤ (⨆ j : y.type, y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) :=
          le_inf hxi_y le_rfl
      _ ≤ ⨆ j, (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) :=
          (iSup_inf_eq _ _).le
      _ ≤ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ functionMk F h_congr := by
          apply iSup_le; intro j
          apply le_iSup_of_le j
          have hyj : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤ y.bval j :=
            inf_le_left.trans inf_le_left
          have hxij : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤
              x.func i =ᴮ y.func j := inf_le_left.trans inf_le_right
          have hxbi : (y.bval j ⊓ x.func i =ᴮ y.func j) ⊓ (Γ ⊓ x.bval i) ≤ x.bval i :=
            inf_le_right.trans inf_le_right
          -- pair (x.func i) (x.func i) ∈ functionMk (from functionMk_self)
          -- We need pair (x.func i) (y.func j) ∈ functionMk
          -- But functionMk sends x.func i to x.func i, not y.func j
          -- We need: x.func i =ᴮ y.func j, so y.func j ≡ x.func i
          -- pair (x.func i) (x.func i) ∈ functionMk, and x.func i =ᴮ y.func j
          -- bv_rw' (H := bv_symm hxij: y.func j =ᴮ x.func i) to get pair (x.func i) (y.func j)
          refine le_inf hyj ?_
          apply bv_rw' (H := bv_symm hxij) (ϕ := fun z => pair (x.func i) z ∈ᴮ functionMk F h_congr)
            (h_congr := B_ext_pair_mem_right)
          exact le_trans hxbi (functionMk_self (h_congr := h_congr))
  -- is_inj functionMk: from the proof structure
  have h_inj : (⊤ : 𝔹) ≤ is_inj (functionMk F h_congr) := by
    -- functionMk F h_congr has type {pair (x.func i) (x.func i) | i}
    -- is_inj says: pair w₁ v₁ ∈ f, pair w₂ v₂ ∈ f, v₁ =ᴮ v₂ → w₁ =ᴮ w₂
    -- From membership extraction: w₁ =ᴮ x.func i, v₁ =ᴮ F i = x.func i
    --                            w₂ =ᴮ x.func j, v₂ =ᴮ F j = x.func j
    -- v₁ =ᴮ v₂ means x.func i =ᴮ x.func j
    -- w₁ =ᴮ x.func i =ᴮ x.func j =ᴮ w₂
    -- This is exactly functionMk_inj_of_inj with h_inj trivially false (no i ≠ j with F i =ᴮ F j → ⊥)
    -- Wait, we can't say F i =ᴮ F j → ⊥ for i ≠ j in general.
    -- Use direct is_inj proof instead:
    apply le_iInf; intro w₁; apply le_iInf; intro w₂
    apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction, top_inf_eq]
    have hmemL : pair w₁ v₁ ∈ᴮ (functionMk F h_congr) ≤
        ⨆ i : x.type, x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i) := by
      simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
    have hmemR : pair w₂ v₂ ∈ᴮ (functionMk F h_congr) ≤
        ⨆ j : x.type, x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j) := by
      simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]; exact le_rfl
    set ctxI := pair w₁ v₁ ∈ᴮ functionMk F h_congr ⊓ pair w₂ v₂ ∈ᴮ functionMk F h_congr ⊓ v₁ =ᴮ v₂
    calc ctxI
        ≤ (⨆ i, x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI :=
          le_inf (inf_le_left.trans (inf_le_left.trans hmemL)) le_rfl
      _ ≤ ⨆ i, (x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI :=
          (iSup_inf_eq _ _).le
      _ ≤ w₁ =ᴮ w₂ := by
          apply iSup_le; intro i
          calc (x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI
              ≤ (⨆ j, x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                  ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI) :=
                le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans hmemR))) le_rfl
            _ ≤ ⨆ j, (x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                  ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI) :=
                (iSup_inf_eq _ _).le
            _ ≤ w₁ =ᴮ w₂ := by
                apply iSup_le; intro j
                set ctxJ := (x.bval j ⊓ pair w₂ v₂ =ᴮ pair (x.func j) (F j)) ⊓
                      ((x.bval i ⊓ pair w₁ v₁ =ᴮ pair (x.func i) (F i)) ⊓ ctxI)
                have hw1xi : ctxJ ≤ w₁ =ᴮ x.func i :=
                  inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left))
                have hv1Fi : ctxJ ≤ v₁ =ᴮ F i :=
                  inf_le_right.trans (inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right))
                have hw2xj : ctxJ ≤ w₂ =ᴮ x.func j :=
                  inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_left)
                have hv2Fj : ctxJ ≤ v₂ =ᴮ F j :=
                  inf_le_left.trans (inf_le_right.trans eq_of_eq_pair_right)
                have hv12 : ctxJ ≤ v₁ =ᴮ v₂ := inf_le_right.trans (inf_le_right.trans inf_le_right)
                -- F i = x.func i, F j = x.func j
                -- v₁ =ᴮ x.func i, v₂ =ᴮ x.func j, v₁ =ᴮ v₂ → x.func i =ᴮ x.func j
                -- w₁ =ᴮ x.func i, w₂ =ᴮ x.func j → w₁ =ᴮ w₂
                have hxi_xj : ctxJ ≤ x.func i =ᴮ x.func j :=
                  bv_trans (bv_symm hv1Fi) (bv_trans hv12 hv2Fj)
                exact bv_trans hw1xi (bv_trans hxi_xj (bv_symm hw2xj))
  -- Combine: injects_into x y via witness functionMk F h_congr
  unfold injects_into
  apply le_iSup_of_le (functionMk F h_congr)
  apply le_inf
  · exact le_inf (le_top.trans h_func) h_total
  · exact le_top.trans h_inj
-- src/bvm_extras.lean:2475
private lemma injects_into_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ injects_into x x :=
  injects_into_of_subset subset_self

-- src/bvm_extras.lean:2478


-- src/bvm_extras.lean:2481


-- src/bvm_extras.lean:2484


-- src/bvm_extras.lean:2486


-- src/bvm_extras.lean:2520


-- src/bvm_extras.lean:2551


-- src/bvm_extras.lean:2638


-- src/bvm_extras.lean:2647


-- src/bvm_extras.lean:2665


-- src/bvm_extras.lean:2671


-- src/bvm_extras.lean:2674


-- src/bvm_extras.lean:2677


-- src/bvm_extras.lean:2680


-- src/bvm_extras.lean:2682


-- src/bvm_extras.lean:2684


-- src/bvm_extras.lean:2694


-- src/bvm_extras.lean:2701


-- src/bvm_extras.lean:2714


-- src/bvm_extras.lean:2717


-- src/bvm_extras.lean:2719


-- src/bvm_extras.lean:2721


-- src/bvm_extras.lean:2723


-- src/bvm_extras.lean:2727


-- src/bvm_extras.lean:2730


-- src/bvm_extras.lean:2736


-- src/bvm_extras.lean:2741


-- src/bvm_extras.lean:2743


end ordinals

-- ============================================================
-- src/bvm_extras.lean:2749-2793: section zorns_lemma
-- ============================================================

section zorns_lemma
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2753


end zorns_lemma

-- ============================================================
-- src/bvm_extras.lean:2795-2821: section CH
-- ============================================================

section CH
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2803


-- src/bvm_extras.lean:2805


-- src/bvm_extras.lean:2807
private lemma CH_iff_CH₂ : ∀ {Γ : 𝔹}, Γ ≤ CH ↔ Γ ≤ CH₂ := by
  intro Γ
  constructor
  · intro H
    -- H : Γ ≤ CH = (D_CH)ᶜ; want Γ ≤ CH₂ = (D_CH₂)ᶜ
    -- Since D_CH₂ ≤ D_CH, we have (D_CH)ᶜ ≤ (D_CH₂)ᶜ
    apply H.trans
    apply compl_le_compl
    -- D_CH₂ = ⨆ x, Ord x ⊓ (ω≺x)ᶜ ⊓ (x≺𝒫ω)ᶜ
    -- D_CH = ⨆ x, Ord x ⊓ ⨆ y, (ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω
    apply iSup_le; intro x
    apply le_iSup_of_le x
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    -- ⨆ y, (ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω: witness y = 𝒫ω
    apply le_iSup_of_le (bv_powerset omega)
    -- (ω≺x)ᶜ ⊓ (x≺𝒫ω)ᶜ ⊓ (𝒫ω ≼ 𝒫ω)
    -- LHS = (Ord x ⊓ (ω≺x)ᶜ) ⊓ (x≺𝒫ω)ᶜ
    refine le_inf (le_inf ?_ ?_) injects_into_refl
    · exact inf_le_left.trans inf_le_right  -- (ω≺x)ᶜ from (Ord x ⊓ (ω≺x)ᶜ) ⊓ (x≺𝒫ω)ᶜ
    · exact inf_le_right                    -- (x≺𝒫ω)ᶜ
  · intro H
    -- H : Γ ≤ CH₂ = (D_CH₂)ᶜ; want Γ ≤ CH = (D_CH)ᶜ
    -- Since D_CH ≤ D_CH₂, we have (D_CH₂)ᶜ ≤ (D_CH)ᶜ
    apply H.trans
    apply compl_le_compl
    -- Goal: D_CH ≤ D_CH₂
    apply iSup_le; intro x
    apply le_iSup_of_le x
    -- Goal: Ord x ⊓ ⨆ y, (ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω ≤ Ord x ⊓ (ω≺x)ᶜ ⊓ (x≺𝒫ω)ᶜ
    -- Target is ((Ord x ⊓ (ω≺x)ᶜ) ⊓ (x≺𝒫ω)ᶜ)
    refine le_inf (le_inf inf_le_left ?_) ?_
    · -- (ω≺x)ᶜ from ⨆ y, (ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω
      -- distribute iSup into the meet, then each branch has (ω≺x)ᶜ
      rw [inf_iSup_eq']; apply iSup_le; intro y
      -- goal: Ord x ⊓ ((ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω) ≤ (ω≺x)ᶜ
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    · -- (x≺𝒫ω)ᶜ from ⨆ y, (ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω via bSet_lt_of_lt_of_le
      rw [inf_iSup_eq']; apply iSup_le; intro y
      -- goal: Ord x ⊓ ((ω≺x)ᶜ ⊓ (x≺y)ᶜ ⊓ y≼𝒫ω) ≤ (x≺𝒫ω)ᶜ
      exact bSet_lt_of_lt_of_le (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)

end CH

end bSet


end CohenSource_BvmExtras

/- Source module: Definitions.Flypitch4.Fol -/
section CohenSource_Fol
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/fol.lean (lines 23-508): Language, preterm, term-level material. -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Fol

/-! ## Valuation helpers (subst_realize) -/





















/-! ## Language -/





variable (L : Language.{u})

/-! ## preterm and term -/





variable {L}









namespace preterm





end preterm









-- term.rec: custom recursion principle via structural recursion










/-! ## lift_term_at — lifting variables -/





































/-! ## subst_term — substitution -/







































/-! ## preformula and formula -/



-- Switch L back to explicit so that `preformula L l` works in type signatures.
-- (After "variable {L}" at line 103, writing "preformula l" has ambiguous L in type positions.)
variable (L)

-- formula: formula L is the type of first-order formulas over language L.


variable {L}































/-! ## lift_formula_at — lifting variables in formulas -/































/-! ## subst_formula — substitution into formulas -/



































/-! ## count_quantifiers and quantifier_free -/









/-! ## prf — the proof system (src/fol.lean lines 816-824) -/









/-! ## Derived proof rules (src/fol.lean lines 832-1103) -/



















































































































/-! ## Theory and consistency (src/fol.lean lines 1105-) -/





/-! ## Structure — L-structures (src/fol.lean line 1109) -/

variable (L)



variable {L}



/-! ## realize_term — realization of terms in a structure -/









/-! ## realize_formula — satisfaction relation -/







private lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realize_formula (subst_realize v (realize_term v s DVec.nil) 0) f xs ↔
    realize_formula v (subst_formula f s 0) xs := by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

private lemma realize_formula_subst_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
    realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs = realize_formula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [realize_formula, lift_formula_at, realize_term_subst_lift]
      exact realize_formula_subst_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula, lift_formula_at]
      exact propext (Iff.imp
        (Iff.of_eq (realize_formula_subst_lift v x m f₁ xs))
        (Iff.of_eq (realize_formula_subst_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ => by
      simp only [realize_formula, lift_formula_at]
      apply propext
      apply forall_congr'
      intro x'
      rw [propext (realize_formula_congr (fun k => subst_realize2_0 v x' x m k) (lift_formula_at f 1 (m + 1)) DVec.nil)]
      exact Iff.of_eq (realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f DVec.nil)

/-! ## Semantic notions — satisfaction and models -/



























/-! ## Soundness (src/fol.lean lines 1247-1261) -/

private lemma formula_soundness {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ A := by
  intro S
  induction H with
  | axm h => intro v hΓ; exact hΓ _ h
  | impI _ ih =>
    intro v hΓ ha
    apply ih
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | impE A _ _ ih₁ ih₂ => intro v hΓ; exact ih₁ v hΓ (ih₂ v hΓ)
  | falsumE _ ih =>
    intro v hΓ
    by_contra ha
    apply ih v
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | allI _ ih =>
    intro v hΓ x
    apply ih
    intro f hf
    rcases hf with ⟨f', hf', rfl⟩
    rw [realize_formula_subst_lift v x 0 f']
    exact hΓ f' hf'
  | allE₂ A t _ ih =>
    intro v hΓ
    rw [← realize_formula_subst0]
    exact ih v hΓ (realize_term v t DVec.nil)
  | ref => intro v _; simp [realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro v hΓ
    have h' := ih₁ v hΓ
    simp only [realize_formula] at h'
    rw [← realize_formula_subst0, ← h', realize_formula_subst0]
    exact ih₂ v hΓ

/-! ## bounded_preterm, bounded_term, closed_preterm (src/fol.lean lines 1265-1660) -/

-- Bring L back to explicit so that bounded_preterm's constructors can refer to the
-- inductive type unambiguously (same pattern as Structure and formula above).
variable (L)



export bounded_preterm (bd_var bd_func bd_app)







variable {L}









namespace bounded_preterm

































end bounded_preterm

namespace closed_preterm







end closed_preterm

/-! ### bounded_term.rec — custom recursion principle -/





/-! ### Lift and substitution — irrel lemmas -/





/-! ### realize_bounded_term -/



















/-! ### lift_bounded_term_at — lifting bounded terms -/













/-! ### subst_bounded_term — substitution in bounded terms -/































/-! ### realize_bounded_term lemmas -/











/-! ## bounded_preformula, bounded_formula, presentence, sentence (src/fol.lean lines 1660-2200) -/

variable (L)



export bounded_preformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)





variable {L}



/-! ### bounded_preformula notations -/

-- Note: ≃ and ⟹ and ∀' are already declared for preformula/preterm above (scoped).
-- We overload them here for bounded_preformula. Since these are scoped notations,
-- we extend existing ones in the Fol namespace.

-- bd_falsum notation conflicts with preformula.falsum ⊥'; we use bd_falsum directly.
-- The bounded equality and implication will reuse the same notation symbols.





















/-! ### bd_apps_rel -/





/-! ### namespace bounded_preformula -/

namespace bounded_preformula















































end bounded_preformula

/-! ### namespace presentence -/

namespace presentence





end presentence

/-! ### Irrel lemmas for bounded formulas -/









/-! ### realize_bounded_formula -/







/-! ### realize_bounded_formula lemmas -/

-- Helper for realize_bounded_formula_iff: structural recursion over f












/-! ### bounded_formula_of_relation -/



/-! ### Recursors for bounded_preformula / bounded_formula (src/fol.lean lines 1984-2038) -/







/-! ### substmax_bounded_formula — substitute the max (last) variable -/



















/-! ### realize_sentence lemmas -/





































private lemma realize_sentence_iff {S : Structure L} (v : ℕ → S) (f : sentence L) :
    realize_sentence S f ↔ realize_formula v f.fst DVec.nil := by
  apply realize_bounded_formula_iff
  intro k hk
  exact absurd hk (Nat.not_lt_zero k)

/-! ### lift_bounded_formula_at — lift bounded formulas -/













/-! ## Sentence theories (src/fol.lean lines 2233-2759) -/














/-! ### All-realize-sentence — a structure models a sentence theory -/



-- Use ⊨ₜ for "structure realizes a sentence theory" (distinct from existing ⊨ₛ)


private lemma all_realize_sentence_of_subset {S : Structure L} {T₁ T₂ : SentTheory L}
    (H : S ⊨ₜ T₂) (h_sub : T₁ ⊆ T₂) : S ⊨ₜ T₁ :=
  fun _ hf => H (h_sub hf)







/-! ### ssatisfied — semantic consequence for sentence theories -/



-- Note: ⊨ₛ is already taken by satisfied_in; use ssatisfied directly.



/-! ### Connection between ssatisfied and satisfied -/



private lemma ssatisfied_of_satisfied {T : SentTheory L} {f : sentence L}
    (H : T.fst ⊨ f.fst) : ssatisfied T f := by
  intro S hS hT
  obtain ⟨s⟩ := hS
  rw [realize_sentence_iff (fun _ => s)]
  apply H
  intro f' hf'
  rcases hf' with ⟨f'', hf'', rfl⟩
  rw [← realize_sentence_iff]
  exact hT hf''





/-! ## Model — bundled structure satisfying a sentence theory -/



namespace Model

variable {T : SentTheory L}







end Model







/-! ### Soundness at sentence level -/

private lemma ssatisfied_soundness {T : SentTheory L} {A : sentence L} (H : T ⊢ₛ' A) :
    ssatisfied T A :=
  ssatisfied_of_satisfied (formula_soundness (Nonempty.some H))



/-! ### Sentence-level is_consistent -/



/-! ### Theory of a structure -/









/-! ### eliminates_quantifiers -/



/-! ### L_empty, T_empty, T_equality -/







/-! ## Section bd_alls (src/fol.lean lines 2706-2757) -/



















end Fol


end CohenSource_Fol

/- Source module: Definitions.Flypitch4.Bfol -/
section CohenSource_Bfol
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bfol.lean lines 1-450:
   Boolean-valued first-order logic — bStructure + early semantics. -/




set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DVec

namespace Fol

section bfol

/-! ## bStructure — boolean-valued L-structure -/



variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]



attribute [simp] bStructure.eq_refl

variable {S : bStructure L β}



private lemma eq_dsymm : ∀ {n} (x y : DVec S n),
    (DVec.map2 S.eq x y).fInf = (DVec.map2 S.eq y x).fInf
  | _, DVec.nil, DVec.nil => rfl
  | _, DVec.cons x xs, DVec.cons y ys => by
      simp [S.eq_symm x y, eq_dsymm xs ys]



private lemma subst_realize_congr1 (v v' : ℕ → S) (x : S) (m : ℕ) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v' x m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]; exact iInf_le _ k
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]; exact iInf_le _ (k - 1)

private lemma subst_realize_congr2 (v : ℕ → S) (x y : S) (m : ℕ) :
    S.eq x y ≤ ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v y m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]

/-! ## boolean_realize_term -/





private lemma boolean_realize_term_subst (v : ℕ → S) :
    ∀ {l} (m : ℕ) (t : @preterm L l) (s : term L) (xs : DVec S l),
    boolean_realize_term
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) t xs =
    boolean_realize_term v (subst_term t s m) xs
  | _, m, preterm.var k, s, _ => by
      simp only [boolean_realize_term, subst_term, subst_realize_lt, subst_realize_gt,
                 subst_realize_var_eq]
      rcases Nat.lt_trichotomy k m with h | h | h
      · simp [h, Nat.lt_asymm h]
      · subst h; simp
      · simp [h, Nat.lt_asymm h]
  | _, _, preterm.func _, _, _ => rfl
  | _, m, preterm.app t₁ t₂, s, xs => by
      simp only [boolean_realize_term, subst_term]
      rw [boolean_realize_term_subst v m t₂ s DVec.nil,
          boolean_realize_term_subst v m t₁ s]



private lemma boolean_realize_term_congr_gen (v v' : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ≤
      S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
  | _, preterm.var k, _, _ => le_trans inf_le_left (iInf_le _ k)
  | _, preterm.func f, xs, xs' => le_trans inf_le_right (S.fun_congr f xs xs')
  | _, preterm.app t₁ t₂, xs, xs' => by
      simp only [boolean_realize_term]
      refine le_trans ?_ (boolean_realize_term_congr_gen v v' t₁
        (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t₂ DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      apply le_inf
      · exact inf_le_left
      · apply le_inf
        · have h2 := boolean_realize_term_congr_gen v v' t₂ DVec.nil DVec.nil
          simp only [DVec.map2, DVec.fInf_nil, inf_top_eq] at h2
          exact le_trans inf_le_left h2
        · exact inf_le_right

private lemma boolean_realize_term_congr_iInf (v v' : ℕ → S) {l} (t : @preterm L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) := by
  have h := boolean_realize_term_congr_gen v v' t xs xs
  simp only [eq_drefl, inf_top_eq] at h
  exact h



/-! ## boolean_realize_formula -/





private lemma boolean_realize_formula_subst : ∀ {l} (v : ℕ → S) (m : ℕ) (f : @preformula L l)
    (s : term L) (xs : DVec S l),
    boolean_realize_formula
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) f xs =
    boolean_realize_formula v (subst_formula f s m) xs
  | _, v, m, preformula.falsum, s, xs => rfl
  | _, v, m, preformula.equal t₁ t₂, s, xs => by
      simp [boolean_realize_term_subst]
  | _, v, m, preformula.rel R, s, xs => rfl
  | _, v, m, preformula.apprel f t, s, xs => by
      simp only [boolean_realize_formula, subst_formula, boolean_realize_term_subst]
      rw [boolean_realize_formula_subst v m f s]
  | _, v, m, preformula.imp f₁ f₂, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1
      · rw [boolean_realize_formula_subst v m f₁ s xs]
      · rw [boolean_realize_formula_subst v m f₂ s xs]
  | _, v, m, preformula.all f, s, xs => by
      simp only [boolean_realize_formula, subst_formula]
      congr 1; funext x
      rw [← boolean_realize_formula_subst (subst_realize v x 0) (m + 1) f s xs]
      apply boolean_realize_formula_congr'
      intro k
      rw [subst_realize2_0, ← boolean_realize_term_subst_lift v x 0, lift_term_def, lift_term2]

private lemma boolean_realize_formula_subst0 {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    boolean_realize_formula (subst_realize v (boolean_realize_term v s DVec.nil) 0) f xs =
    boolean_realize_formula v (subst_formula f s 0) xs := by
  have h := boolean_realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs



private lemma boolean_realize_formula_congr_gen : ∀ (v v' : ℕ → S) {l} (f : @preformula L l)
    (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
    boolean_realize_formula v f xs ≤ boolean_realize_formula v' f xs'
  | v, v', _, preformula.falsum, _, _ => inf_le_right
  | v, v', _, preformula.equal t₁ t₂, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      -- Goal: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v' t₂)
      refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₂ DVec.nil))
      apply le_inf
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v' t₁)(brt v t₂)
        refine le_trans ?_ (S.eq_trans (boolean_realize_term v t₁ DVec.nil))
        apply le_inf
        · -- Need: I ⊓ ... ≤ S.eq(brt v' t₁)(brt v t₁)
          -- = S.eq(brt v t₁)(brt v' t₁) by symm, and I ≤ that by congr_iInf
          rw [S.eq_symm (boolean_realize_term v' t₁ DVec.nil) (boolean_realize_term v t₁ DVec.nil)]
          exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₁ DVec.nil)
        · exact inf_le_right  -- I ⊓ S.eq... ≤ S.eq(brt v t₁)(brt v t₂)
      · -- Need: I ⊓ S.eq(brt v t₁)(brt v t₂) ≤ S.eq(brt v t₂)(brt v' t₂)
        exact le_trans inf_le_left (boolean_realize_term_congr_iInf v v' t₂ DVec.nil)
  | v, v', _, preformula.rel R, xs, xs' => by
      simp only [boolean_realize_formula]
      exact le_trans (inf_le_inf inf_le_right le_rfl) (S.rel_congr R xs xs')
  | v, v', _, preformula.apprel f t, xs, xs' => by
      simp only [boolean_realize_formula]
      refine le_trans ?_ (boolean_realize_formula_congr_gen v v' f
        (DVec.cons (boolean_realize_term v t DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      -- Need: I ⊓ xs_eq ⊓ brf v f (brt v t :: xs) ≤
      --         I ⊓ (S.eq(brt v t)(brt v' t) ⊓ xs_eq) ⊓ brf v f (brt v t :: xs)
      -- brf does not change; so need to weaken I ⊓ xs_eq to I ⊓ (S.eq ⊓ xs_eq)
      apply le_inf
      · -- I ⊓ xs_eq ⊓ brf ≤ I ⊓ (S.eq ⊓ xs_eq)
        apply le_inf
        · exact le_trans inf_le_left inf_le_left  -- ≤ I
        · apply le_inf
          · -- ≤ S.eq(brt v t)(brt v' t)
            exact le_trans (le_trans inf_le_left inf_le_left)
              (boolean_realize_term_congr_iInf v v' t DVec.nil)
          · exact le_trans inf_le_left inf_le_right  -- ≤ xs_eq
      · exact inf_le_right  -- ≤ brf v f (brt v t :: xs)
  | v, v', _, preformula.imp f₁ f₂, xs, xs' => by
      simp only [boolean_realize_formula, imp, inf_sup_left]
      apply sup_le_sup
      · -- Need: I ⊓ xs_eq ⊓ b_f₁ᶜ ≤ b_f₁'ᶜ
        apply le_neg_of_inf_eq_bot
        -- From IH with v↔v', xs↔xs': I' ⊓ xs_eq' ⊓ b_f₁' ≤ b_f₁
        -- I' = (⨅ k, S.eq (v' k) (v k)) = I  (by eq_symm)
        -- xs_eq' = (xs'.map2 S.eq xs).fInf = xs_eq  (by eq_dsymm)
        have key := boolean_realize_formula_congr_gen v' v f₁ xs' xs
        rw [show (⨅ k : ℕ, S.eq (v' k) (v k)) = (⨅ k : ℕ, S.eq (v k) (v' k)) from
              iInf_congr fun k => S.eq_symm _ _,
            ← eq_dsymm xs xs'] at key
        have bot := sub_eq_bot_of_le key
        -- bot: b_f₁ᶜ ⊓ (I ⊓ xs_eq ⊓ b_f₁') = ⊥
        -- Need: b_f₁' ⊓ (I ⊓ xs_eq ⊓ b_f₁ᶜ) = ⊥
        -- These are equal by commutativity and associativity of ⊓
        have : boolean_realize_formula v' f₁ xs' ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               (boolean_realize_formula v f₁ xs)ᶜ) =
               (boolean_realize_formula v f₁ xs)ᶜ ⊓
               ((⨅ k, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
               boolean_realize_formula v' f₁ xs') := by ac_rfl
        rw [this]; exact bot
      · exact boolean_realize_formula_congr_gen v v' f₂ xs xs'
  | v, v', _, preformula.all f, DVec.nil, DVec.nil => by
      simp only [boolean_realize_formula, DVec.map2, DVec.fInf_nil, inf_top_eq]
      rw [le_iInf_iff]
      intro x
      refine le_trans ?_ (boolean_realize_formula_congr_gen (subst_realize v x 0)
        (subst_realize v' x 0) f DVec.nil DVec.nil)
      simp only [DVec.map2, DVec.fInf_nil, inf_top_eq]
      apply le_inf
      · exact le_trans inf_le_left (subst_realize_congr1 v v' x 0)
      · exact le_trans inf_le_right (iInf_le _ x)

private lemma boolean_realize_formula_congr (v v' : ℕ → S) {l} (f : @preformula L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ boolean_realize_formula v f xs ≤
    boolean_realize_formula v' f xs := by
  have key := boolean_realize_formula_congr_gen v v' f xs xs
  have hd : (DVec.map2 S.eq xs xs).fInf = ⊤ := eq_drefl xs
  rw [hd, inf_top_eq] at key
  exact le_trans (le_inf le_rfl le_top) (by rw [inf_top_eq]; exact key)

private lemma boolean_realize_formula_subst_congr (v : ℕ → S) (s s' : term L) :
    ∀ {m l} (f : @preformula L l) (xs : DVec S l),
    S.eq (boolean_realize_term v (lift_term s m) DVec.nil)
         (boolean_realize_term v (lift_term s' m) DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s m) xs ≤
    boolean_realize_formula v (subst_formula f s' m) xs := by
  intro m l f xs
  rw [← boolean_realize_formula_subst v m f s xs,
      ← boolean_realize_formula_subst v m f s' xs]
  refine le_trans ?_
    (boolean_realize_formula_congr
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m)
      (subst_realize v (boolean_realize_term v (lift_term s' m) DVec.nil) m) f xs)
  apply inf_le_inf_right
  exact subst_realize_congr2 v _ _ m

private lemma boolean_realize_formula_subst_congr0 (v : ℕ → S) (s s' : term L) {l} (f : @preformula L l)
    (xs : DVec S l) :
    S.eq (boolean_realize_term v s DVec.nil) (boolean_realize_term v s' DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s 0) xs ≤
    boolean_realize_formula v (subst_formula f s' 0) xs := by
  have h := boolean_realize_formula_subst_congr v s s' (m := 0) f xs
  simp only [lift_term_zero] at h
  exact h



/-! ## Satisfiability — boolean_realize_formula_glb, bstatisfied -/













/-! ## boolean_formula_soundness -/

/-- Soundness for boolean-valued semantics: if Γ ⊢ A, then Γ ⊨ᵤ[β] A. -/
private lemma boolean_formula_soundness {Γ : Set (formula L)} {A : formula L}
    (H : Γ ⊢ A) : Γ ⊨ᵤ[β] A := by
  induction H with
  | axm h => exact bstatisfied_of_mem h
  | impI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [deduction_simp]
    refine le_trans ?_ (ih S v)
    rw [inf_comm, iInf_insert]
  | impE A _ _ ih₁ ih₂ =>
    intro S v
    have h1 := ih₁ S v
    have h2 := ih₂ S v
    simp only [boolean_realize_formula] at h1
    exact le_trans (le_inf h1 h2) (imp_inf_le _ _)
  | falsumE _ ih =>
    intro S v
    apply le_of_sub_eq_bot
    apply bot_unique
    refine le_trans ?_ (ih S v)
    rw [iInf_insert, boolean_realize_formula_not]
  | allI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [le_iInf_iff]
    intro x
    refine le_trans ?_ (ih S _)
    apply le_iInf
    intro f
    apply le_iInf
    rintro ⟨f', hf', rfl⟩
    rw [boolean_realize_formula_subst_lift]
    exact le_trans (iInf_le _ f') (iInf_le _ hf')
  | allE₂ A t _ ih =>
    intro S v
    rw [← boolean_realize_formula_subst0]
    exact le_trans (ih S v) (iInf_le _ _)
  | ref Γ t =>
    intro S v
    simp [boolean_realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro S v
    refine le_trans ?_ (boolean_realize_formula_subst_congr0 v s t f DVec.nil)
    exact le_inf (ih₁ S v) (ih₂ S v)

/-! ## boolean_realize_bounded_term -/





























/-! ## boolean_realize_bounded_formula -/



/-! ## boolean_realize_sentence — src/bfol.lean:456-459 -/





/-! ## boolean_realize_bounded_formula_eq — src/bfol.lean:461-475 -/







/-! ## boolean_realize_bounded_formula_congr — src/bfol.lean:489-503 -/



/-! ## boolean_realize_bounded_formula_irrel' — src/bfol.lean:513-528 -/





/-! ## boolean_realize_bounded_formula_cast_eq_irrel — src/bfol.lean:536-538 -/



/-! ## basic simp lemmas for boolean_realize_sentence — src/bfol.lean:543-559 -/























/-! ## boolean_realize_bounded_formula_bd_apps_rel — src/bfol.lean:596-602 -/



/-! ## boolean_realize_cast_bounded_formula — src/bfol.lean:604-619 -/





/-! ## boolean_realize_sentence_bd_apps_rel — src/bfol.lean:621-634 -/











/-! ## forced_in, all_forced_in — src/bfol.lean:647-658 -/











/-! ## forced — src/bfol.lean:674-677 -/





/-! ## bsatisfied_of_forced, forced_of_bsatisfied — src/bfol.lean:680-698 -/







private lemma forced_absurd {S : bStructure L β} {f : sentence L} {Γ : β}
    (H₁ : Γ ⊩[S] f) (H₂ : Γ ⊩[S] (bd_not f : sentence L)) : Γ ⊩[S] (bd_falsum : sentence L) := by
  show Γ ≤ ⊥
  have hH₂ : Γ ≤ (⟦f⟧[S])ᶜ := by
    calc Γ ≤ ⟦(bd_not f : sentence L)⟧[S] := H₂
      _ = (⟦f⟧[S])ᶜ := boolean_realize_sentence_not
  have : Γ ≤ ⟦f⟧[S] ⊓ (⟦f⟧[S])ᶜ := le_inf H₁ hH₂
  rw [inf_compl_eq_bot] at this
  exact this

/-! ## bModel — src/bfol.lean:720-721 -/



/-! ## boolean_soundness, unprovable_of_model_neg — src/bfol.lean:730-739 -/

private theorem boolean_soundness {T : SentTheory L} {A : sentence L} (H : T ⊢ₛ' A) :
    T ⊨[β] A :=
  forced_of_bsatisfied (boolean_formula_soundness (β := β) (Classical.choice H))

private lemma unprovable_of_model_neg {T : SentTheory L} {f : sentence L}
    (S : bStructure L β) (H_model : ⊤ ⊩ₜ[S] T) [H_nonempty : Nonempty S]
    {Γ : β} (H_nonzero : (⊥ : β) < Γ) (H : Γ ⊩[S] (bd_not f : sentence L)) :
    ¬(T ⊢ₛ' f) := by
  intro Hp
  have hforced := boolean_soundness (β := β) Hp H_nonempty
  rw [inf_axioms_top_of_models H_model] at hforced
  have hfabs : Γ ⊩[S] (bd_falsum : sentence L) :=
    forced_absurd (le_trans le_top hforced) H
  -- hfabs : Γ ⊩[S] bd_falsum = Γ ≤ ⊥
  exact absurd (lt_of_lt_of_le H_nonzero hfabs) (lt_irrefl ⊥)

/-! ## boolean_realize_subst_preterm — src/bfol.lean:741-761 -/





/-! ## boolean_realize_sentence_bd_alls — src/bfol.lean:763-778 -/



/-! ## consis_of_exists_bmodel — src/bfol.lean:785-793 -/



/-! ## subst0_bounded_formula_not — src/bfol.lean:799-801 -/



/-! ## subst0_bounded_formula_and — src/bfol.lean:803-805 -/



/-! ## boolean_realize_bounded_formula_insert_lift — src/bfol.lean:854-872 -/



/-! ## boolean_realize_formula_insert_lift2 — src/bfol.lean:874-879 -/



/-! ## boolean_realize_subst_formula0 — src/bfol.lean:881-897 -/



end bfol

end Fol


end CohenSource_Bfol

/- Source module: Definitions.Flypitch4.Completeness -/
section CohenSource_Completeness
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/completeness.lean (59 lines) — Task 20



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Fol

open Lhom

universe u

variable {L : Language.{u}}

/-!
## satisfied_of_provable
Soundness: provability implies semantic consequence.
-/



/-!
## completeness_for_inconsistent_theories
For an inconsistent theory, provability and semantic entailment coincide trivially.
-/



/-!
## model_existence
T is consistent iff there is a nonempty model of T.
-/

private theorem model_existence (T : SentTheory L) :
    T.is_consistent ↔ ∃ M : Structure L, Nonempty M.carrier ∧ all_realize_sentence M T := by
  constructor
  · intro hT
    -- Build the term model of the complete henkinization, then reduct back to L
    let M' := term_model (completion_of_henkinization_complete hT)
                         (completion_of_henkinization_is_henkin hT)
    let M : Structure L := Lhom.reduct (henkin_language_canonical_map 0) M'
    refine ⟨M, ?_, ?_⟩
    · -- nonemptiness: term_model' T = Quotient (closed_term L) (term_setoid T) is nonempty
      -- We get a constant from has_enough_constants: use bd_const c as a witness
      rw [show M.carrier = M'.carrier from Lhom.reduct_coe M']
      show Nonempty (term_model' (completion_of_henkinization hT))
      obtain ⟨C, _⟩ := completion_of_henkinization_is_henkin hT
      exact ⟨@Quotient.mk'' _ (term_setoid _) (bd_const (C bd_falsum))⟩
    · -- T satisfaction
      exact reduct_of_complete_henkinization_models_T hT
  · intro h_ex
    -- A model of T yields consistency: any proof of ⊥ from T would be unsound
    obtain ⟨M, H_nonempty, H_sat⟩ := h_ex
    intro h_prov
    have : ssatisfied T (bd_falsum : sentence L) := ssatisfied_soundness h_prov
    exact (this H_nonempty H_sat).elim

/-!
## nonempty_model_of_consis
A consistent theory has a nonempty model.
-/



/-!
## completeness
The Gödel completeness theorem: T ⊢ₛ' ψ ↔ ssatisfied T ψ.
-/



/-!
## compactness
Semantic compactness: T ⊨ f iff some finite subset of T semantically entails f.
-/



end Fol


end CohenSource_Completeness

/- Source module: Definitions.Flypitch4.Forcing -/
section CohenSource_Forcing
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/forcing.lean (567 lines) — Task 18 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Compatibility with the source port's Mathlib revision.


open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

-- ============================================================
-- src/forcing.lean:34-103: section cardinal_preservation
-- ============================================================

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing.lean:36-48


-- src/forcing.lean:50-56


-- src/forcing.lean:58-62


-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)



end cardinal_preservation

end bSet

open bSet

-- ============================================================
-- src/forcing.lean:107-121: namespace PSet
-- ============================================================

namespace PSet

-- src/forcing.lean:109: ℵ₁ (as PSet)


-- src/forcing.lean:111: ℵ₂ (as PSet)


-- src/forcing.lean:113


-- src/forcing.lean:115-120: Union lemmas (not needed for the main result)

end PSet

open PSet

-- ============================================================
-- src/forcing.lean:125-133: 𝔹_cohen and instances
-- ============================================================



local notation "𝔹" => 𝔹_cohen





-- src/forcing.lean:134


-- src/forcing.lean:136


-- Type equality lemmas for cast operations
-- These hold because check x has .type = x.Type by the definition of check








-- src/forcing.lean:149-176: cast helper lemmas










-- src/forcing.lean:178-179


local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191




-- src/forcing.lean:202-203


-- src/forcing.lean:205-209


-- src/forcing.lean:211-214: structure 𝒞


-- src/forcing.lean:216


-- src/forcing.lean:223-245: ι definition


open CantorSpace

-- src/forcing.lean:249-250


-- src/forcing.lean:252-272: 𝒞_dense_basis


-- src/forcing.lean:274-284: 𝒞_dense


-- src/forcing.lean:286-288


-- src/forcing.lean:292-299


-- src/forcing.lean:301-303


-- src/forcing.lean:305-319: 𝒞_nonzero


-- src/forcing.lean:323-350: 𝒞_disjoint_row


-- src/forcing.lean:352-353


-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real















-- src/forcing.lean:379-386


-- src/forcing.lean:388-398


-- src/forcing.lean:400-406




end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457


-- src/forcing.lean:459-466


-- src/forcing.lean:468-487


-- src/forcing.lean:489-504


-- src/forcing.lean:507-509




-- src/forcing.lean:513-529: cohen_real.mk_ext


-- src/forcing.lean:531-532


-- src/forcing.lean:534-546


-- src/forcing.lean:548-550




-- src/forcing.lean:552-562


-- src/forcing.lean:564-565
private theorem neg_CH₂ : (⊤ : 𝔹) ≤ CH₂ᶜ :=
  (Lattice.bv_iff_neg CH_iff_CH₂).mp neg_CH

end neg_CH

end bSet


end CohenSource_Forcing

/- Source module: Definitions.Flypitch4.Zfc -/
section CohenSource_Zfc
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================







-- ============================================================
-- The Boolean-valued V model (src/zfc.lean:48-113)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]





variable (β)










variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================



















-- ============================================================
-- Simp lemmas for boolean_realize (src/zfc.lean:142-176)
-- ============================================================




















-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================













-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅




-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w




-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y




-- axiom schema of strong collection (src/zfc.lean:208-211)











-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y



-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z



-- axiom of infinity (src/zfc.lean:332-347)



-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y



-- Zorn's lemma (src/zfc.lean:363-376)



-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================







-- ============================================================
-- Functional-relation formulas (src/zfc.lean:402-470)
-- ============================================================





































-- ============================================================
-- The CH formula (src/zfc.lean:481-502)
-- ============================================================



private lemma CH_f_is_CH : ⟦CH_f⟧[V β] = CH₂ := by
  -- L3 proof: simp [-substmax_bounded_formula, CH_f, CH₂, neg_supr, sup_assoc, h1, h2, lattice.imp]
  -- where h1, h2 reduce substmax/subst0 by refl.
  have h1 : ∀ x : V β, boolean_realize_bounded_formula (DVec.cons x DVec.nil)
      (substmax_bounded_formula at_most_f ω') DVec.nil =
      boolean_realize_bounded_formula
        (DVec.cons x (DVec.cons (bSet.omega : V β) DVec.nil)) at_most_f DVec.nil := by
    intro x; rfl
  have h2 : ∀ x : V β, boolean_realize_bounded_formula (DVec.cons x DVec.nil)
      (subst0_bounded_formula at_most_f (Powerset omega')) DVec.nil =
      boolean_realize_bounded_formula
        (DVec.cons (bv_powerset (bSet.omega : V β)) (DVec.cons x DVec.nil)) at_most_f DVec.nil := by
    intro x; rfl
  simp only [CH_f, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_or, Ord_f_is_Ord, h1, h2, realize_at_most_f,
             V_forall, imp, CH₂, compl_iSup, compl_inf, compl_compl, sup_assoc]



private lemma neg_CH_f_sound {Γ : β} : (Γ ⊩[V β] (bd_not CH_f : sentence L_ZFC)) ↔ Γ ≤ CH₂ᶜ := by
  change _ ≤ _ ↔ _ ≤ _
  rw [boolean_realize_sentence_not, CH_f_is_CH]

-- ============================================================
-- CH is unprovable from ZFC (src/zfc.lean:508-536)
-- ============================================================

open PSet Cardinal

section CH_unprovable

local notation "𝔹" => 𝔹_cohen

private lemma V_𝔹_cohen_models_neg_CH : ⊤ ⊩[V 𝔹] (bd_not CH_f : sentence L_ZFC) := by
  rw [neg_CH_f_sound]; exact neg_CH₂



private theorem CH_f_unprovable : ¬ (ZFC ⊢ₛ' CH_f) :=
  unprovable_of_model_neg (V 𝔹) bSet_models_ZFC nontrivial_bot_lt_top V_𝔹_cohen_models_neg_CH

end CH_unprovable

open collapse_algebra

section neg_CH_unprovable







end neg_CH_unprovable

-- ============================================================
-- CH as a first-order formula (src/zfc.lean:538-552)
-- ============================================================

section CH_formula_sec










end CH_formula_sec


end CohenSource_Zfc

/- Source module: Solutions.Work_Cohen_NativeModel -/
section CohenSource_Work_Cohen_NativeModel
set_option autoImplicit false



/-!
**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Original forcing and completeness proofs: Jesse Han and Floris van Doorn.
Lean 4 port: Ian Klatzco, with Claude; Apache-2.0,
commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.

This model uses Flypitch's expanded language. It is not yet the mission's
membership-language model; that requires separate semantic bridges.
-/

namespace ContinuumHypothesis.Cohen

private theorem expanded_countermodel_exists_cohenProof07 :
    ∃ M : Fol.Structure _root_.L_ZFC,
      Nonempty M.carrier ∧ Fol.all_realize_sentence M _root_.ZFC ∧
      ¬ Fol.realize_sentence M _root_.CH_f := by
  have hCons := Fol.consis_not_of_not_provable _root_.CH_f_unprovable
  obtain ⟨M, hM, hSat⟩ :=
    (Fol.model_existence (insert (Fol.bd_not _root_.CH_f) _root_.ZFC)).mp hCons
  refine ⟨M, hM, ?_, ?_⟩
  · exact Fol.all_realize_sentence_of_subset hSat (Set.subset_insert _ _)
  · have h := hSat (Set.mem_insert (Fol.bd_not _root_.CH_f) _root_.ZFC)
    exact Fol.realize_sentence_not.mp h

end ContinuumHypothesis.Cohen




end CohenSource_Work_Cohen_NativeModel


theorem solution : @Exists.{3} (Fol.Structure.{1} L_ZFC) fun M =>
  And (Nonempty.{2} (@Fol.Structure.carrier.{1} L_ZFC M))
    (And (@Fol.all_realize_sentence.{1} L_ZFC M ZFC) (Not (@Fol.realize_sentence.{1} L_ZFC M CH_f))) :=
  @ContinuumHypothesis.Cohen.expanded_countermodel_exists_cohenProof07
