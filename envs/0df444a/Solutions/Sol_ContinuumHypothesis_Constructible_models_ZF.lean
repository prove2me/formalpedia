-- Prove2me | solution 1 for ContinuumHypothesis.Constructible.models_ZF
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T23:53:36.948003+00:00
-- url     : https://prove2.me/submissions/1bab6a59-bbe1-4ab1-8d2b-4e7bb505e80f

import Definitions.Def_CH_Constructible

/-!
**Formalization credit:** Wentao Li (Victor), under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

Development of the ZF axioms in the external constructible universe.
Source: Andrew Marks, Set Theory (January 31, 2026), Definition 20.2,
Lemmas 20.3 and 20.5, printed pp. 86–87:
https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf.

The external reflection argument below uses Mathlib's Skolem closure and the
strong ambient universe: small sets of constructible objects have bounded
constructibility levels. It is not an internal construction in arbitrary ZF models.
-/

open FirstOrder FirstOrder.Language
open ContinuumHypothesis

namespace ContinuumHypothesis.Constructible
noncomputable section
open Classical
set_option Elab.async false

private theorem mem_definableSubsets_subset {a b : ZFSet.{0}}
    (h : b ∈ definableSubsets a) : b ⊆ a :=
  ZFSet.mem_powerset.mp (ZFSet.mem_sep.mp h).1

private theorem self_mem_definableSubsets (a : ZFSet.{0}) :
    a ∈ definableSubsets a := by
  rw [definableSubsets, ZFSet.mem_sep]
  refine ⟨by simp, 0, ⊤, Fin.elim0, ?_⟩
  intro x
  simp [x.property]

private theorem subset_definableSubsets_of_transitive {a : ZFSet.{0}}
    (ha : a.IsTransitive) : a ⊆ definableSubsets a := by
  intro b hb
  rw [definableSubsets, ZFSet.mem_sep]
  refine ⟨ZFSet.mem_powerset.mpr (ha.subset_of_mem hb), 1,
    Relations.formula₂ (SetRel.mem : setLang.Relations 2)
      (Term.var 0) (Term.var 1), (fun _ => ⟨b, hb⟩), ?_⟩
  intro x
  rfl

private theorem definableSubsets_transitive {a : ZFSet.{0}}
    (ha : a.IsTransitive) : (definableSubsets a).IsTransitive := by
  intro b hb x hx
  exact subset_definableSubsets_of_transitive ha
    (mem_definableSubsets_subset hb hx)

private theorem level_transitive (α : Ordinal.{0}) : (level α).IsTransitive := by
  induction α using Ordinal.limitRecOn with
  | zero => simp [ZFSet.IsTransitive]
  | add_one α ih =>
    rw [level_add_one]
    exact definableSubsets_transitive ih
  | limit α h ih =>
    rw [level_limit α h]
    exact ZFSet.IsTransitive.iUnion (fun i => ih i.toOrd.val i.toOrd.property)

private theorem level_subset_add_one (α : Ordinal.{0}) :
    level α ⊆ level (α + 1) := by
  rw [level_add_one]
  exact subset_definableSubsets_of_transitive (level_transitive α)

private theorem level_mono : Monotone level := by
  intro α β h
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
    have : α = 0 := le_antisymm h bot_le
    subst α
    exact le_rfl
  | add_one β ih =>
    rcases h.lt_or_eq with hlt | rfl
    · exact (ih (Order.lt_succ_iff.mp hlt)).trans (level_subset_add_one β)
    · exact le_rfl
  | limit β hb ih =>
    rcases h.eq_or_lt with rfl | hlt
    · exact le_rfl
    · rw [level_limit β hb]
      intro x hx
      apply ZFSet.mem_iUnion.mpr
      refine ⟨Ordinal.ToType.mk ⟨α, hlt⟩, ?_⟩
      simpa using hx

private theorem constructible_of_mem {x y : ZFSet.{0}}
    (hy : IsConstructible y) (hxy : x ∈ y) : IsConstructible x := by
  obtain ⟨α, hα⟩ := hy
  exact ⟨α, (level_transitive α).mem_trans hxy hα⟩

private theorem mem_level_limit {α : Ordinal.{0}} (h : Order.IsSuccLimit α)
    {x : ZFSet.{0}} : x ∈ level α ↔ ∃ β < α, x ∈ level β := by
  rw [level_limit α h, ZFSet.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.toOrd.val, i.toOrd.property, hi⟩
  · rintro ⟨β, hβ, hx⟩
    refine ⟨Ordinal.ToType.mk ⟨β, hβ⟩, ?_⟩
    simpa using hx

private theorem family_bounded {ι : Type*} [Small.{0} ι] (f : ι → Carrier) :
    ∃ α : Ordinal.{0}, ∀ i, (f i).val ∈ level α := by
  let ranks : ι → Ordinal.{0} := fun i => (f i).property.choose
  refine ⟨⨆ i, ranks i, fun i => ?_⟩
  exact level_mono (Ordinal.le_iSup ranks i) (f i).property.choose_spec

private def stage (α : Ordinal.{0}) : setLang.Substructure Carrier where
  carrier := {x | x.val ∈ level α}
  fun_mem := fun f => Empty.elim f

private instance stageSmall (α : Ordinal.{0}) : Small.{0} (stage α) := by
  let f : stage α → level α := fun x => ⟨x.val.val, x.property⟩
  exact small_of_injective (f := f) (fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : level α => z.val) h)))

private def extension (α : Ordinal.{0}) : setLang.ElementarySubstructure Carrier :=
  (Substructure.closure (setLang.sum setLang.skolem₁) (stage α : Set Carrier)).elementarySkolem₁Reduct

private instance extensionSmall (α : Ordinal.{0}) : Small.{0} (extension α) := by
  have : Small.{0} (stage α : Set Carrier) := stageSmall α
  change Small.{0} (Substructure.closure (setLang.sum setLang.skolem₁) (stage α : Set Carrier))
  exact Substructure.small_closure

private theorem stage_subset_extension (α : Ordinal.{0}) :
    (stage α : Set Carrier) ⊆ extension α :=
  Substructure.subset_closure

private def extensionBound (α : Ordinal.{0}) : Ordinal.{0} :=
  (family_bounded (fun x : extension α => x.val)).choose

private def step (α : Ordinal.{0}) : Ordinal.{0} := max (α + 1) (extensionBound α)

private theorem extension_subset_step (α : Ordinal.{0}) :
    (extension α : Set Carrier) ⊆ stage (step α) := by
  intro x hx
  exact level_mono (le_max_right (α + 1) (extensionBound α))
    ((family_bounded (fun x : extension α => x.val)).choose_spec ⟨x, hx⟩)

private def seq (α : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => α
  | n + 1 => step (seq α n)

private theorem seq_strictMono (α : Ordinal.{0}) : StrictMono (seq α) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Order.lt_succ (seq α n)).trans_le (le_max_left _ _)

private def reflectingOrdinal (α : Ordinal.{0}) : Ordinal.{0} := ⨆ n, seq α n

private theorem seq_lt_reflectingOrdinal (α : Ordinal.{0}) (n : ℕ) :
    seq α n < reflectingOrdinal α :=
  (seq_strictMono α (Nat.lt_succ_self n)).trans_le (Ordinal.le_iSup (seq α) (n+1))

private theorem reflectingOrdinal_limit (α : Ordinal.{0}) :
    Order.IsSuccLimit (reflectingOrdinal α) := by
  rw [Order.isSuccLimit_iff_of_orderBot]
  refine ⟨ne_of_gt (lt_of_le_of_lt bot_le (seq_lt_reflectingOrdinal α 0)), ?_⟩
  apply Order.isSuccPrelimit_of_succ_lt
  intro β hβ
  obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hβ
  exact (Order.succ_le_of_lt hn).trans_lt (seq_lt_reflectingOrdinal α n)

private theorem mem_reflecting_level (α : Ordinal.{0}) {x : ZFSet.{0}} :
    x ∈ level (reflectingOrdinal α) ↔ ∃ n, x ∈ level (seq α n) := by
  rw [mem_level_limit (reflectingOrdinal_limit α)]
  constructor
  · rintro ⟨β, hβ, hx⟩
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hβ
    exact ⟨n, level_mono hn.le hx⟩
  · rintro ⟨n, hn⟩
    exact ⟨seq α n, seq_lt_reflectingOrdinal α n, hn⟩

private theorem reflecting_stage_elementary (α : Ordinal.{0}) :
    (stage (reflectingOrdinal α)).IsElementary := by
  apply Substructure.isElementary_of_exists
  intro n φ x a ha
  let indices : Fin n → ℕ := fun i =>
    ((mem_reflecting_level α).mp (x i).property).choose
  let N : ℕ := Finset.univ.sup indices
  have hxN (i : Fin n) : ((x i).val).val ∈ level (seq α N) := by
    exact level_mono ((seq_strictMono α).monotone
      (Finset.le_sup (f := indices) (Finset.mem_univ i)))
      ((mem_reflecting_level α).mp (x i).property).choose_spec
  let S := extension (seq α N)
  let params : Fin n → S := fun i =>
    ⟨(x i).val, stage_subset_extension (seq α N) (hxN i)⟩
  have hex : φ.ex.Realize (default : Empty → Carrier) (S.subtype ∘ params) := by
    exact BoundedFormula.realize_ex.mpr ⟨a, ha⟩
  have hexS : φ.ex.Realize (default : Empty → S) params := by
    apply (S.subtype.map_boundedFormula φ.ex default params).mp
    simpa only [Unique.eq_default] using hex
  obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.mp hexS
  have hbmem : (b : Carrier) ∈ stage (reflectingOrdinal α) :=
    level_mono (Ordinal.le_iSup (seq α) (N+1))
      (extension_subset_step (seq α N) b.property)
  refine ⟨⟨(b : Carrier), hbmem⟩, ?_⟩
  have hh := (S.subtype.map_boundedFormula φ default (Fin.snoc params b)).mpr hb
  simp only [Unique.eq_default, Fin.comp_snoc] at hh
  exact hh

private theorem exists_reflecting_stage (α : Ordinal.{0}) :
    ∃ β ≥ α, (stage β).IsElementary := by
  exact ⟨reflectingOrdinal α, (seq_lt_reflectingOrdinal α 0).le,
    reflecting_stage_elementary α⟩

private def levelToStage (α : Ordinal.{0}) : level α ≃[setLang] stage α where
  toFun := fun x => ⟨⟨x.val, ⟨α, x.property⟩⟩, x.property⟩
  invFun := fun x => ⟨x.val.val, x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_fun' := fun f => Empty.elim f
  map_rel' := fun r _ => by cases r; rfl

private theorem reflecting_realize {α : Ordinal.{0}} (h : (stage α).IsElementary)
    {n : ℕ} (φ : setLang.Formula (Fin n)) (v : Fin n → level α) :
    φ.Realize (fun i => (⟨(v i).val, ⟨α, (v i).property⟩⟩ : Carrier)) ↔
      φ.Realize v := by
  exact (h φ (levelToStage α ∘ v)).trans
    (StrongHomClass.realize_formula (levelToStage α) φ)

private theorem bounded_comprehension {n : ℕ}
    (φ : setLang.Formula (Fin (n+1))) (p : Fin n → Carrier)
    (s : ZFSet.{0})
    (hs : ∀ x : Carrier, φ.Realize (Fin.cases x p) → x.val ∈ s) :
    ∃ b : Carrier, ∀ x : Carrier, x.val ∈ b.val ↔ φ.Realize (Fin.cases x p) := by
  let D := {x : Carrier // φ.Realize (Fin.cases x p)}
  have : Small.{0} D := by
    let f : D → s := fun x => ⟨x.val.val, hs x.val x.property⟩
    exact small_of_injective (f := f) (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : s => z.val) h)))
  let family : Fin n ⊕ D → Carrier := Sum.elim p Subtype.val
  obtain ⟨α, hα⟩ := family_bounded family
  obtain ⟨β, hαβ, hβ⟩ := exists_reflecting_stage α
  have hp (i : Fin n) : (p i).val ∈ level β :=
    level_mono hαβ (hα (Sum.inl i))
  have hD (x : Carrier) (hx : φ.Realize (Fin.cases x p)) : x.val ∈ level β :=
    level_mono hαβ (hα (Sum.inr ⟨x, hx⟩))
  let q : Fin n → level β := fun i => ⟨(p i).val, hp i⟩
  have transfer (z : level β) :
      φ.Realize (Fin.cases (⟨z.val, ⟨β, z.property⟩⟩ : Carrier) p) ↔
        φ.Realize (Fin.cases z q) := by
    have ht := reflecting_realize hβ φ (Fin.cases z q)
    have heq : (fun y : level β => (⟨y.val, ⟨β, y.property⟩⟩ : Carrier)) ∘
        (Fin.cases z q : Fin (n+1) → level β) =
        Fin.cases (⟨z.val, ⟨β, z.property⟩⟩ : Carrier) p := by
      funext i
      cases i using Fin.cases <;> rfl
    dsimp only [Function.comp_def] at heq
    rw [heq] at ht
    exact ht
  let b : ZFSet.{0} := ZFSet.sep (fun z =>
    ∃ hz : z ∈ level β, φ.Realize (Fin.cases (⟨z, hz⟩ : level β) q)) (level β)
  have hb : IsConstructible b := by
    refine ⟨β+1, ?_⟩
    rw [level_add_one, definableSubsets, ZFSet.mem_sep]
    refine ⟨ZFSet.mem_powerset.mpr ZFSet.sep_subset, n, φ, q, ?_⟩
    intro x
    simp [b, x.property]
  refine ⟨⟨b, hb⟩, fun x => ?_⟩
  constructor
  · intro hx
    change x.val ∈ b at hx
    dsimp only [b] at hx
    obtain ⟨_, hz, hφ⟩ := ZFSet.mem_sep.mp hx
    exact (transfer ⟨x.val, hz⟩).mpr hφ
  · intro hx
    have hxβ := hD x hx
    have ht := (transfer ⟨x.val, hxβ⟩).mp hx
    change x.val ∈ b
    exact ZFSet.mem_sep.mpr ⟨hxβ, hxβ, ht⟩

private theorem formula_congr {M : Type*} [setLang.Structure M]
    (φ : SFormula) {v w : ℕ → M}
    (h : ∀ i ∈ φ.freeVarFinset, v i = w i) : Formula.Realize φ v ↔ Formula.Realize φ w := by
  exact (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := fun i : φ.freeVarFinset => v i.val) (xs := default) v (fun _ => rfl)).symm.trans
    (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
      (v := fun i : φ.freeVarFinset => v i.val) (xs := default) w
      (fun i => h i.val i.property))

private theorem named_comprehension (φ : SFormula) (v : ℕ → Carrier)
    (x : ℕ) (s : ZFSet.{0})
    (hs : ∀ z : Carrier, Formula.Realize φ (Function.update v x z) → z.val ∈ s) :
    ∃ b : Carrier, ∀ z : Carrier,
      z.val ∈ b.val ↔ Formula.Realize φ (Function.update v x z) := by
  let e := Fintype.equivFin φ.freeVarFinset
  let g : φ.freeVarFinset → Fin (Fintype.card φ.freeVarFinset + 1) :=
    fun i => if i.val = x then 0 else (e i).succ
  let ψ : setLang.Formula (Fin (Fintype.card φ.freeVarFinset + 1)) :=
    φ.restrictFreeVar g
  let p : Fin (Fintype.card φ.freeVarFinset) → Carrier := fun i => v (e.symm i).val
  have hψ (z : Carrier) : ψ.Realize (Fin.cases z p) ↔
      Formula.Realize φ (Function.update v x z) := by
    apply BoundedFormula.realize_restrictFreeVar (Function.update v x z)
    intro i
    by_cases hi : i.val = x <;> simp [g, p, hi]
  obtain ⟨b, hb⟩ := bounded_comprehension ψ p s (fun z hz => hs z ((hψ z).mp hz))
  exact ⟨b, fun z => (hb z).trans (hψ z)⟩

private theorem realize_all {M : Type*} [setLang.Structure M]
    (v : ℕ → M) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.all i φ) v ↔ ∀ z : M, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.all, Formula.realize_iAlls]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → M) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · intro h z
    exact h (fun _ => z)
  · intro h u
    exact h (u ())

private theorem realize_ex {M : Type*} [setLang.Structure M]
    (v : ℕ → M) (i : ℕ) (φ : SFormula) :
    Formula.Realize (SFormula.ex i φ) v ↔ ∃ z : M, Formula.Realize φ (Function.update v i z) := by
  rw [SFormula.ex, Formula.realize_iExs]
  simp only [Formula.realize_relabel]
  have heq (u : Unit → M) :
      (Sum.elim v u) ∘ (fun j => if j = i then Sum.inr () else Sum.inl j) =
        Function.update v i (u ()) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  simp only [heq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u (), hu⟩
  · rintro ⟨z, hz⟩
    exact ⟨fun _ => z, hz⟩

private theorem close_of_all (φ : SFormula) (h : ∀ v : ℕ → Carrier, Formula.Realize φ v) :
    Carrier ⊨ SFormula.close φ := by
  change Formula.Realize (SFormula.close φ) (default : Empty → Carrier)
  rw [SFormula.close, Formula.realize_iAlls]
  intro v
  exact Formula.realize_relabel.mpr (h _)

@[simp] private theorem realize_mem (v : ℕ → Carrier) (i j : ℕ) :
    Formula.Realize (SFormula.mem i j) v ↔ (v i).val ∈ (v j).val := by rfl

@[simp] private theorem realize_eq (v : ℕ → Carrier) (i j : ℕ) :
    Formula.Realize (SFormula.eq i j) v ↔ v i = v j := by rfl

private def levelCarrier (α : Ordinal.{0}) : Carrier :=
  ⟨level α, ⟨α+1, by rw [level_add_one]; exact self_mem_definableSubsets _⟩⟩

private theorem carrier_ext (x y : Carrier)
    (h : ∀ z : Carrier, z.val ∈ x.val ↔ z.val ∈ y.val) : x = y := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (h ⟨z, constructible_of_mem x.property hz⟩).mp hz
  · intro hz
    exact (h ⟨z, constructible_of_mem y.property hz⟩).mpr hz

private theorem carrier_subset (x y : Carrier) :
    (∀ z : Carrier, z.val ∈ x.val → z.val ∈ y.val) ↔ x.val ⊆ y.val := by
  constructor
  · intro h z hz
    exact h ⟨z, constructible_of_mem x.property hz⟩ hz
  · intro h z hz
    exact h hz

private theorem carrier_foundation (x : Carrier)
    (hne : ∃ y : Carrier, y.val ∈ x.val) :
    ∃ y : Carrier, y.val ∈ x.val ∧ ∀ z : Carrier, z.val ∈ x.val → z.val ∉ y.val := by
  obtain ⟨y, hy, hmin⟩ := ZFSet.mem_wf.has_min (x.val : Set ZFSet.{0})
    ⟨hne.choose.val, hne.choose_spec⟩
  exact ⟨⟨y, constructible_of_mem x.property hy⟩, hy,
    fun z hz hzy => hmin z.val hz hzy⟩

private theorem carrier_collection (a : Carrier) (R : Carrier → Carrier → Prop)
    (h : ∀ x : Carrier, x.val ∈ a.val → ∃ y : Carrier, R x y) :
    ∃ b : Carrier, ∀ x : Carrier, x.val ∈ a.val →
      ∃ y : Carrier, y.val ∈ b.val ∧ R x y := by
  let elem : a.val → Carrier := fun x => ⟨x.val, constructible_of_mem a.property x.property⟩
  let f : a.val → Carrier := fun x => (h (elem x) x.property).choose
  obtain ⟨α, hα⟩ := family_bounded f
  refine ⟨levelCarrier α, fun x hx => ?_⟩
  exact ⟨f ⟨x.val, hx⟩, hα ⟨x.val, hx⟩, (h (elem ⟨x.val, hx⟩) hx).choose_spec⟩

private theorem formula_update_fresh (φ : SFormula) (v : ℕ → Carrier)
    (b x : ℕ) (B z : Carrier) (hb : b ∉ φ.freeVarFinset) (_hxb : x ≠ b) :
    Formula.Realize φ (Function.update (Function.update v b B) x z) ↔
      Formula.Realize φ (Function.update v x z) := by
  apply formula_congr
  intro i hi
  have hib : i ≠ b := fun h => hb (h ▸ hi)
  by_cases hix : i = x <;> simp [hix, hib]

private theorem comprehension_witness (ψ : SFormula) (v : ℕ → Carrier)
    (x b : ℕ) (s : ZFSet.{0}) (hxb : x ≠ b)
    (hb : ∀ B z : Carrier,
      Formula.Realize ψ (Function.update (Function.update v b B) x z) ↔
        Formula.Realize ψ (Function.update v x z))
    (hs : ∀ z : Carrier, Formula.Realize ψ (Function.update v x z) → z.val ∈ s) :
    Formula.Realize (SFormula.ex b (SFormula.all x (SFormula.mem x b ⇔ ψ))) v := by
  obtain ⟨B, hB⟩ := named_comprehension ψ v x s hs
  rw [realize_ex]
  refine ⟨B, ?_⟩
  rw [realize_all]
  intro z
  rw [Formula.realize_iff, realize_mem]
  simpa only [Function.update_self, Function.update_of_ne hxb.symm] using
    (hB z).trans (hb B z).symm

private theorem models_extensionality : Carrier ⊨ SFormula.close SFormula.extensionality := by
  apply close_of_all
  intro v
  simpa [SFormula.extensionality, realize_all, Function.update_apply] using carrier_ext

private theorem models_foundation : Carrier ⊨ SFormula.close SFormula.foundation := by
  apply close_of_all
  intro v
  have hmath : ∀ x : Carrier, (∃ y : Carrier, y.val ∈ x.val) →
      ∃ y : Carrier, y.val ∈ x.val ∧ ¬ ∃ z : Carrier, z.val ∈ y.val ∧ z.val ∈ x.val := by
    intro x hx
    obtain ⟨y, hy, hmin⟩ := carrier_foundation x hx
    exact ⟨y, hy, fun ⟨z, hz, hzx⟩ => hmin z hzx hz⟩
  simpa [SFormula.foundation, realize_all, realize_ex, Function.update_apply] using hmath

private theorem models_pairing : Carrier ⊨ SFormula.close SFormula.pairing := by
  apply close_of_all
  intro v
  rw [SFormula.pairing, realize_all]
  intro a
  rw [realize_all]
  intro b
  apply comprehension_witness (SFormula.eq 1009 0 ⊔ SFormula.eq 1009 1)
    (Function.update (Function.update v 0 a) 1 b) 1009 2 {a.val, b.val}
    (by decide) (by intro B z; simp)
  intro z hz
  simp at hz
  rcases hz with rfl | rfl <;> simp

private theorem models_union : Carrier ⊨ SFormula.close SFormula.union := by
  apply close_of_all
  intro v
  rw [SFormula.union, realize_all]
  intro a
  apply comprehension_witness (SFormula.ex 3 (SFormula.mem 3 0 ⊓ SFormula.mem 2 3))
    (Function.update v 0 a) 2 1 (ZFSet.sUnion a.val) (by decide)
    (by intro B z; simp [realize_ex])
  intro z hz
  have h : ∃ y : Carrier, y.val ∈ a.val ∧ z.val ∈ y.val := by
    simpa [realize_ex, Function.update_apply] using hz
  obtain ⟨y, hy, hz⟩ := h
  exact ZFSet.mem_sUnion.mpr ⟨y.val, hy, hz⟩

private theorem models_powerset : Carrier ⊨ SFormula.close SFormula.powerset := by
  apply close_of_all
  intro v
  rw [SFormula.powerset, realize_all]
  intro a
  apply comprehension_witness (SFormula.subset 1007 0)
    (Function.update v 0 a) 1007 1 (ZFSet.powerset a.val) (by decide)
    (by intro B z; simp [SFormula.subset, realize_all])
  intro z hz
  apply ZFSet.mem_powerset.mpr
  apply (carrier_subset z a).mp
  simpa [SFormula.subset, realize_all, Function.update_apply] using hz

private theorem models_separation (σ : SFormula) (hσ : SFormula.IsSeparation σ) :
    Carrier ⊨ SFormula.close σ := by
  obtain ⟨φ, x, a, b, hxa, hxb, hab, hb, rfl⟩ := hσ
  apply close_of_all
  intro v
  rw [realize_all]
  intro A
  let w := Function.update v a A
  apply comprehension_witness (SFormula.mem x a ⊓ φ) w x b A.val hxb
  · intro B z
    rw [Formula.realize_inf, Formula.realize_inf]
    apply and_congr
    · simp [hxa.symm, hab]
    · exact formula_update_fresh φ w b x B z hb hxb
  · intro z hz
    have hz' := (Formula.realize_inf.mp hz).1
    simpa [w, Function.update_apply, hxa.symm] using hz'

private theorem models_replacement (σ : SFormula) (hσ : SFormula.IsReplacement σ) :
    Carrier ⊨ SFormula.close σ := by
  obtain ⟨φ, x, y, y', a, b, hnd, hb, hy', rfl⟩ := hσ
  have hxnot : x ∉ [y, y', a, b] := (List.nodup_cons.mp hnd).1
  have hynot : y ∉ [y', a, b] := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hxa : x ≠ a := fun h => hxnot (by simp [h])
  have hxb : x ≠ b := fun h => hxnot (by simp [h])
  have hyb : y ≠ b := fun h => hynot (by simp [h])
  have hab : a ≠ b := by
    intro h
    subst b
    simp at hnd
  apply close_of_all
  intro v
  rw [realize_all]
  intro A
  rw [Formula.realize_imp]
  intro hfun
  let w := Function.update v a A
  let R : Carrier → Carrier → Prop := fun X Y =>
    Formula.Realize φ (Function.update (Function.update w x X) y Y)
  have hR (X : Carrier) (hX : X.val ∈ A.val) : ∃ Y : Carrier, R X Y := by
    have h := (realize_all _ _ _).mp hfun X
    have hex := (Formula.realize_imp.mp h) (by
      simpa [realize_mem, Function.update_apply, hxa.symm] using hX)
    obtain ⟨Y, hY⟩ := (realize_ex _ _ _).mp hex
    exact ⟨Y, (Formula.realize_inf.mp hY).1⟩
  obtain ⟨B, hB⟩ := carrier_collection A R hR
  rw [realize_ex]
  refine ⟨B, ?_⟩
  rw [realize_all]
  intro X
  rw [Formula.realize_imp, realize_mem]
  intro hX
  have hXA : X.val ∈ A.val := by
    simpa [w, Function.update_apply, hxa.symm, hab] using hX
  obtain ⟨Y, hY, hφ⟩ := hB X hXA
  rw [realize_ex]
  refine ⟨Y, ?_⟩
  rw [Formula.realize_inf, realize_mem]
  constructor
  · simpa [Function.update_apply, hyb.symm, hxb.symm] using hY
  · apply (formula_congr φ
      (v := Function.update (Function.update (Function.update w b B) x X) y Y)
      (w := Function.update (Function.update w x X) y Y) ?_).mpr hφ
    intro i hi
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    by_cases hiy : i = y
    · simp [hiy]
    · by_cases hix : i = x <;> simp [Function.update_apply, hiy, hix, hib]

private theorem successor_mem_definableSubsets {a x : ZFSet.{0}}
    (ha : a.IsTransitive) (hx : x ∈ a) : insert x x ∈ definableSubsets a := by
  rw [definableSubsets, ZFSet.mem_sep]
  refine ⟨ZFSet.mem_powerset.mpr ?_, 1,
    (Term.var 0).equal (Term.var 1) ⊔
      Relations.formula₂ (SetRel.mem : setLang.Relations 2) (Term.var 0) (Term.var 1),
    (fun _ => (⟨x, hx⟩ : a)), ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · exact ha.mem_trans hz hx
  · intro z
    simp only [ZFSet.mem_insert_iff, Formula.realize_sup, Formula.realize_equal,
      Formula.realize_rel₂, Term.realize_var, Fin.cases_zero,
      Subtype.ext_iff]
    rfl

private theorem carrier_infinity :
    ∃ w : Carrier, (∃ z : Carrier, z.val = ∅ ∧ z.val ∈ w.val) ∧
      ∀ z : Carrier, z.val ∈ w.val →
        ∃ s : Carrier, s.val = insert z.val z.val ∧ s.val ∈ w.val := by
  let α := reflectingOrdinal 0
  have hα : Order.IsSuccLimit α := reflectingOrdinal_limit 0
  have h0α : (0 : Ordinal.{0}) < α := seq_lt_reflectingOrdinal 0 0
  have h1α : (0 : Ordinal.{0}) + 1 ≤ α := Order.succ_le_of_lt h0α
  refine ⟨levelCarrier α, ?_, ?_⟩
  · refine ⟨levelCarrier 0, level_zero, ?_⟩
    change level 0 ∈ level α
    exact level_mono h1α (by rw [level_add_one]; exact self_mem_definableSubsets _)
  · intro z hz
    obtain ⟨β, hβ, hzβ⟩ := (mem_level_limit hα).mp hz
    have hs : insert z.val z.val ∈ level (β+1) := by
      rw [level_add_one]
      exact successor_mem_definableSubsets (level_transitive β) hzβ
    have hsα : insert z.val z.val ∈ level α := level_mono (hα.succ_lt hβ).le hs
    exact ⟨⟨insert z.val z.val, ⟨α, hsα⟩⟩, rfl, hsα⟩

private theorem models_infinity : Carrier ⊨ SFormula.close SFormula.infinity := by
  apply close_of_all
  intro v
  obtain ⟨w, he, hs⟩ := carrier_infinity
  rw [SFormula.infinity, realize_ex]
  refine ⟨w, ?_⟩
  simp only [SFormula.isInductive, Formula.realize_inf]
  constructor
  · obtain ⟨z, hz, hzw⟩ := he
    rw [realize_ex]
    refine ⟨z, ?_⟩
    simpa [SFormula.isEmpty, realize_all, Function.update_apply, hz] using hzw
  · rw [realize_all]
    intro z
    rw [Formula.realize_imp, realize_mem]
    intro hzw
    have hzw' : z.val ∈ w.val := by simpa [Function.update_apply] using hzw
    obtain ⟨s, hsval, hsw⟩ := hs z hzw'
    rw [realize_ex]
    refine ⟨s, ?_⟩
    simpa [SFormula.isSucc, realize_all, Function.update_apply, hsval,
      Subtype.ext_iff, or_comm] using hsw

private theorem models_ZF_core : Carrier ⊨ ZF := by
  constructor
  intro τ hτ
  change τ ∈ SFormula.close '' SFormula.ZFAxioms at hτ
  obtain ⟨σ, hσ, rfl⟩ := hτ
  rcases hσ with (hbase | hsep) | hrep
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbase
    rcases hbase with rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extensionality
    · exact models_foundation
    · exact models_pairing
    · exact models_union
    · exact models_powerset
    · exact models_infinity
  · exact models_separation σ hsep
  · exact models_replacement σ hrep


end
end ContinuumHypothesis.Constructible

theorem solution : Constructible.Carrier ⊨ ZF :=
  Constructible.models_ZF_core
