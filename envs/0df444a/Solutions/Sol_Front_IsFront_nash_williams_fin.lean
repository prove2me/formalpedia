-- Prove2me | solution 1 for Front.IsFront.nash_williams_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:15.651891+00:00
-- url     : https://prove2.me/submissions/da0d4ded-f1ce-4036-a509-941749c1ccaa

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Data.Finset.Sort
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_NashWilliams
public import Theorems.Thm_Front_IsFront_nil_not_mem_iff
public import Theorems.Thm_Front_IsFront_ray_rank_lt
public import Theorems.Thm_Front_IsFront_shrink_rank_le
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_Front_shrink_shrink
public import Theorems.Thm_Set_Infinite_exists_strictMono
public import Theorems.Thm_exists_infinite_fiber_nat
attribute [local simp] Front.isInit_nil


section
@[expose] public section
open Set List
noncomputable section
namespace Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
private theorem nw_trivial (hF : IsFront F M) (h0 : [] ∈ F) (S : Set (List ℕ)) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
      (shrink F (M ∘ e) ⊆ S ∨ Disjoint (shrink F (M ∘ e)) S) := by
  refine ⟨id, strictMono_id, ?_⟩
  have hFeq : F = {[]} := by by_contra hne; exact (hF.nil_not_mem_iff.mpr hne) h0
  rw [Function.comp_id]
  have hsingle : ∀ s, s ∈ shrink F M → s = [] := by
    intro s hs; have := hs.1; rw [hFeq] at this; simpa using this
  by_cases hS : ([] : List ℕ) ∈ S
  · exact Or.inl fun s hs => (hsingle s hs) ▸ hS
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro s hs hsS; rw [hsingle s hs] at hsS; exact hS hsS
private theorem nw_step (hF : IsFront F M) (h0 : [] ∉ F) (S : Set (List ℕ))
    (ih : ∀ {M' : ℕ → ℕ} {F' : Set (List ℕ)} (hF' : IsFront F' M'), hF'.rank < hF.rank →
      ∀ S' : Set (List ℕ), ∃ e : ℕ → ℕ, StrictMono e ∧
        (shrink F' (M' ∘ e) ⊆ S' ∨ Disjoint (shrink F' (M' ∘ e)) S'))
    (T : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M}) :
    ∃ T' : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M},
      (∀ i, T'.1 i ∈ Set.range T.1) ∧ (∀ i, T.1 0 < T'.1 i) ∧
      ∃ col : Bool,
        (col = true → shrink (ray F (T.1 0)) T'.1 ⊆ ray S (T.1 0)) ∧
        (col = false → Disjoint (shrink (ray F (T.1 0)) T'.1) (ray S (T.1 0))) := by
  obtain ⟨B, hBmono, hBsub⟩ := T
  change ∃ T' : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M},
      (∀ i, T'.1 i ∈ Set.range B) ∧ (∀ i, B 0 < T'.1 i) ∧
      ∃ col : Bool,
        (col = true → shrink (ray F (B 0)) T'.1 ⊆ ray S (B 0)) ∧
        (col = false → Disjoint (shrink (ray F (B 0)) T'.1) (ray S (B 0)))
  have hnM : B 0 ∈ Set.range M := hBsub 0
  have hRay : IsFront (ray F (B 0)) (rayEnum M (B 0)) := hF.ray_isFront_mem h0 hnM
  have hBtail_mono : StrictMono (fun i => B (i + 1)) := fun a b hab => hBmono (by omega)
  have hBtail_gt : ∀ i, B 0 < B (i + 1) := fun i => hBmono (by omega)
  have hBtail_ray : ∀ i, B (i + 1) ∈ Set.range (rayEnum M (B 0)) := fun i => by
    rw [mem_range_rayEnum_iff hF.mono]; exact ⟨hBsub (i + 1), hBtail_gt i⟩
  obtain ⟨E, hE, hEcomp⟩ :=
    exists_strictMono_comp (rayEnum_strictMono hF.mono (B 0)) hBtail_mono hBtail_ray
  have hG : IsFront (shrink (ray F (B 0)) (rayEnum M (B 0) ∘ E)) (rayEnum M (B 0) ∘ E) :=
    shrink_isFront hRay hE
  have hrank_lt : hG.rank < hF.rank :=
    lt_of_le_of_lt (hRay.shrink_rank_le hE) (hF.ray_rank_lt h0 hnM)
  obtain ⟨e, he, hdisj⟩ := ih hG hrank_lt (ray S (B 0))
  have hAeq : (rayEnum M (B 0) ∘ E) ∘ e = fun i => B (e i + 1) := by
    funext i; simp only [Function.comp_apply, hEcomp]
  have hA'mono : StrictMono (fun i => B (e i + 1)) :=
    fun a b hab => hBmono (by have := he hab; omega)
  have hA'M : ∀ i, B (e i + 1) ∈ Set.range M := fun i => hBsub (e i + 1)
  have hcollapse :
      shrink (shrink (ray F (B 0)) (rayEnum M (B 0) ∘ E)) ((rayEnum M (B 0) ∘ E) ∘ e)
        = shrink (ray F (B 0)) (fun i => B (e i + 1)) := by
    rw [shrink_shrink (Set.range_comp_subset_range e (rayEnum M (B 0) ∘ E)), hAeq]
  refine ⟨⟨fun i => B (e i + 1), hA'mono, hA'M⟩, fun i => ⟨e i + 1, rfl⟩,
    fun i => hBmono (by omega), ?_⟩
  rcases hdisj with hsub | hdis
  · exact ⟨true, fun _ => by rw [← hcollapse]; exact hsub, fun h => absurd h (by simp)⟩
  · exact ⟨false, fun h => absurd h (by simp), fun _ => by rw [← hcollapse]; exact hdis⟩
private theorem nw_of_rank : ∀ (α : Ordinal) (M : ℕ → ℕ) (F : Set (List ℕ))
    (hF : IsFront F M) (S : Set (List ℕ)), hF.rank = α →
    ∃ e : ℕ → ℕ, StrictMono e ∧
      (shrink F (M ∘ e) ⊆ S ∨ Disjoint (shrink F (M ∘ e)) S) := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro M F hF S hrank
    by_cases h0 : [] ∈ F
    · exact nw_trivial hF h0 S
    · -- Nontrivial front `[] ∉ F`: the ray recursion.
      -- The induction hypothesis, packaged as a rank-bounded oracle for `nw_step`.
      have ih : ∀ {M' : ℕ → ℕ} {F' : Set (List ℕ)} (hF' : IsFront F' M'),
          hF'.rank < hF.rank → ∀ S' : Set (List ℕ), ∃ e : ℕ → ℕ, StrictMono e ∧
            (shrink F' (M' ∘ e) ⊆ S' ∨ Disjoint (shrink F' (M' ∘ e)) S') :=
        fun {M'} {F'} hF' hlt S' => IH hF'.rank (hrank ▸ hlt) M' F' hF' S' rfl
      -- Iterate the step by dependent choice.
      choose g hnest hgt gcol hcolT hcolF using nw_step hF h0 S ih
      let st : ℕ → {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M} :=
        fun k => Nat.rec
          (motive := fun _ => {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M})
          ⟨M, hF.mono, fun i => ⟨i, rfl⟩⟩ (fun _ p => g p) k
      have hstep : ∀ k, st (k + 1) = g (st k) := fun _ => rfl
      let nn : ℕ → ℕ := fun k => (st k).1 0
      let cc : ℕ → Bool := fun k => gcol (st k)
      -- `nn` is a strictly increasing sequence of elements of `M`.
      have hnn_mono : StrictMono nn := by
        apply strictMono_nat_of_lt_succ
        intro k; have h := hgt (st k) 0; rw [← hstep k] at h; exact h
      have hnn_mem : ∀ k, nn k ∈ Set.range M := fun k => (st k).2.2 0
      -- Nesting of the tails, closed under `≤`.
      have hnest1 : ∀ k, ∀ i, (st (k + 1)).1 i ∈ Set.range (st k).1 := by
        intro k; rw [hstep k]; exact hnest (st k)
      have hnest_le : ∀ k l, Set.range (st (k + l)).1 ⊆ Set.range (st k).1 := by
        intro k l
        induction l with
        | zero => exact subset_rfl
        | succ m ih =>
          refine subset_trans ?_ ih
          rintro _ ⟨j, rfl⟩; exact hnest1 (k + m) j
      -- Pigeonhole: infinitely many steps share a colour `i`.
      obtain ⟨i, hi⟩ := exists_infinite_fiber_nat cc
      obtain ⟨φ, hφmono, hφmem⟩ := hi.exists_strictMono
      have hφcol : ∀ j, cc (φ j) = i := hφmem
      -- The chosen infinite subset `M ∘ e = {nn (φ j)}`.
      have hy_mono : StrictMono (fun j => nn (φ j)) := hnn_mono.comp hφmono
      have hy_mem : ∀ j, nn (φ j) ∈ Set.range M := fun j => hnn_mem (φ j)
      obtain ⟨e, he, hey⟩ := exists_strictMono_comp hF.mono hy_mono hy_mem
      refine ⟨e, he, ?_⟩
      -- Every element of the restricted front splits as `nn (φ j0) :: t` with `t` in the
      -- monochromatic sub-front at step `φ j0`.
      have key : ∀ s ∈ shrink F (M ∘ e), ∃ j0 t, s = nn (φ j0) :: t ∧
          t ∈ shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1 := by
        rintro s ⟨hsF, hsE⟩
        have hsne : s ≠ [] := fun h => h0 (h ▸ hsF)
        obtain ⟨a, t, rfl⟩ : ∃ a t, s = a :: t := by
          cases s with
          | nil => exact absurd rfl hsne
          | cons a t => exact ⟨a, t, rfl⟩
        have ha : a ∈ Set.range (M ∘ e) := hsE a List.mem_cons_self
        rw [hey] at ha
        obtain ⟨j0, hj0⟩ := ha
        have hj0 : nn (φ j0) = a := hj0
        refine ⟨j0, t, by rw [hj0], ?_, ?_⟩
        · change nn (φ j0) :: t ∈ F
          rw [hj0]; exact hsF
        · intro x hx
          have hxE : x ∈ Set.range (M ∘ e) := hsE x (List.mem_cons_of_mem a hx)
          rw [hey] at hxE
          obtain ⟨j', hj'⟩ := hxE
          have hj' : nn (φ j') = x := hj'
          have hax : a < x := (List.pairwise_cons.mp (hF.sorted (a :: t) hsF)).1 x hx
          rw [← hj0, ← hj'] at hax
          have hjj : φ j0 < φ j' := hnn_mono.lt_iff_lt.mp hax
          have hsub2 : Set.range (st (φ j')).1 ⊆ Set.range (st (φ j0 + 1)).1 := by
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hjj : φ j0 + 1 ≤ φ j')
            rw [hd]; exact hnest_le (φ j0 + 1) d
          rw [← hj']; exact hsub2 ⟨0, rfl⟩
      -- Read off the uniform colour.
      cases i with
      | true =>
        refine Or.inl fun s hs => ?_
        obtain ⟨j0, t, hst, ht⟩ := key s hs
        have hsubset : shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1 ⊆ ray S (nn (φ j0)) := by
          have h := hcolT (st (φ j0)) (hφcol j0); rwa [← hstep (φ j0)] at h
        rw [hst]; exact hsubset ht
      | false =>
        refine Or.inr ?_
        rw [Set.disjoint_left]
        intro s hs hsS
        obtain ⟨j0, t, hst, ht⟩ := key s hs
        have hdisj2 :
            Disjoint (shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1) (ray S (nn (φ j0))) := by
          have h := hcolF (st (φ j0)) (hφcol j0); rwa [← hstep (φ j0)] at h
        rw [Set.disjoint_left] at hdisj2
        rw [hst] at hsS; exact hdisj2 ht hsS
private theorem nw_fin_aux {κ : Type*} (c : List ℕ → κ) (P : Finset κ) :
    ∀ (M : ℕ → ℕ) (F : Set (List ℕ)), IsFront F M → (∀ s ∈ F, c s ∈ P) →
      ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
        ∀ s ∈ shrink F (M ∘ e), c s = col := by
  classical
  induction P using Finset.strongInductionOn with
  | _ P IH =>
    intro M F hF hb
    -- Density gives an element of `F`, hence a color `a ∈ P` to blur on.
    obtain ⟨s0, hs0, -⟩ := hF.dense id strictMono_id
    have ha : c s0 ∈ P := hb s0 hs0
    -- Blur `c` to the 2-coloring "is it `c s0`?" and apply the base theorem.
    obtain ⟨e₁, he₁, hcase⟩ := nw_of_rank hF.rank M F hF {s | c s = c s0} rfl
    rcases hcase with hsub | hdis
    · exact ⟨e₁, he₁, c s0, fun s hs => hsub hs⟩
    · have hF' : IsFront (shrink F (M ∘ e₁)) (M ∘ e₁) := shrink_isFront hF he₁
      have hb' : ∀ s ∈ shrink F (M ∘ e₁), c s ∈ P.erase (c s0) := fun s hs =>
        Finset.mem_erase.mpr ⟨Set.disjoint_left.mp hdis hs, hb s hs.1⟩
      obtain ⟨e₂, he₂, col, hcol⟩ :=
        IH (P.erase (c s0)) (Finset.erase_ssubset ha) (M ∘ e₁) _ hF' hb'
      refine ⟨e₁ ∘ e₂, he₁.comp he₂, col, fun s hs => ?_⟩
      have hcol2 :
          shrink (shrink F (M ∘ e₁)) ((M ∘ e₁) ∘ e₂) = shrink F (M ∘ (e₁ ∘ e₂)) :=
        shrink_shrink (Set.range_comp_subset_range e₂ (M ∘ e₁))
      exact hcol s (hcol2 ▸ hs)
end Front
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
namespace IsFront
theorem _root_.solution (hF : IsFront F M) {κ : Type*} [Finite κ]
    (c : List ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ s ∈ shrink F (M ∘ e), c s = col := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  exact nw_fin_aux c Finset.univ M F hF (fun s _ => Finset.mem_univ _)
end IsFront
end Front
