-- Prove2me | solution 1 for BrinSquier.freeAbelianBasis_infinite_of_not_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T09:30:40.563091+00:00
-- url     : https://prove2.me/submissions/4956625a-6dc2-4137-9ba1-64923c38809a

import Theorems.Thm_HomeoLine_pairwise_disjoint_zpow_image
import Theorems.Thm_BrinSquier_compact_closure_supp_commutator
import Theorems.Thm_BrinSquier_closure_supp_commutator_subset
import Theorems.Thm_HomeoLine_exists_mem_closure_apply_gt
import Theorems.Thm_HomeoLine_zpow_moves_of_moves
import Definitions.Def_BrinSquier
import Mathlib
import Theorems.Thm_BrinSquier_supp_conj
import Theorems.Thm_BrinSquier_supp_finite_components
import Theorems.Thm_HomeoLine_mem_connectedComponentIn_of_fixes_compl
import Theorems.Thm_TopCover_finite_components_of_finite_cover

namespace BS_32
open BrinSquier

/-- The set of connected components of `U`. -/
def Comps (U : Set ℝ) : Set (Set ℝ) := {C | ∃ x ∈ U, C = connectedComponentIn U x}

/-- `supp f ∪ supp g` has finitely many components, being covered by the components of
each piece. -/
theorem comps_union_finite {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) :
    (Comps (supp f ∪ supp g)).Finite := by
  classical
  have h1 : (Comps (supp f)).Finite := BrinSquier.supp_finite_components hf
  have h2 : (Comps (supp g)).Finite := BrinSquier.supp_finite_components hg
  haveI := h1.to_subtype
  haveI := h2.to_subtype
  refine TopCover.finite_components_of_finite_cover
    (ι := {C // C ∈ Comps (supp f)} ⊕ {C // C ∈ Comps (supp g)})
    (Sum.elim (fun C => (C : Set ℝ)) (fun C => (C : Set ℝ))) ?_ ?_ ?_
  · rintro (⟨C, x, hx, rfl⟩ | ⟨C, x, hx, rfl⟩)
    · exact isPreconnected_connectedComponentIn
    · exact isPreconnected_connectedComponentIn
  · rintro (⟨C, x, hx, rfl⟩ | ⟨C, x, hx, rfl⟩)
    · exact (connectedComponentIn_subset _ _).trans Set.subset_union_left
    · exact (connectedComponentIn_subset _ _).trans Set.subset_union_right
  · intro x hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion.2 ⟨Sum.inl ⟨_, x, hx, rfl⟩, mem_connectedComponentIn hx⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inr ⟨_, x, hx, rfl⟩, mem_connectedComponentIn hx⟩

/-- The components of `U` that a map's moved set actually meets. -/
def Met (U : Set ℝ) (w : ℝ ≃o ℝ) : Set (Set ℝ) := {C ∈ Comps U | (supp w ∩ C).Nonempty}

lemma met_subset (U : Set ℝ) (w : ℝ ≃o ℝ) : Met U w ⊆ Comps U := fun _ h => h.1

lemma met_finite {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) (w : ℝ ≃o ℝ) :
    (Met (supp f ∪ supp g) w).Finite :=
  (comps_union_finite hf hg).subset (met_subset _ _)

end BS_32

namespace BS_32b
open BrinSquier BS_32

/-- The moved set of a homeomorphism is open. -/
theorem isOpen_supp (f : ℝ ≃o ℝ) : IsOpen (supp f) :=
  isOpen_ne_fun (OrderIso.continuous f) continuous_id

/-- A compact subset of `U` meets a component of `U` in a compact set: the closure of the
component adds nothing, because a point of `U` in that closure is already in the component. -/
theorem compact_inter_comp {U K : Set ℝ} (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    {x : ℝ} (hx : x ∈ U) :
    IsCompact (K ∩ connectedComponentIn U x) := by
  have heq : K ∩ closure (connectedComponentIn U x) = K ∩ connectedComponentIn U x := by
    apply Set.Subset.antisymm _ (Set.inter_subset_inter_right _ subset_closure)
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hyU : y ∈ U := hKU hy.1
    have hopen : IsOpen (connectedComponentIn U y) := hU.connectedComponentIn
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy.2 _ hopen (mem_connectedComponentIn hyU)
    have e1 : connectedComponentIn U y = connectedComponentIn U z := connectedComponentIn_eq hz1
    have e2 : connectedComponentIn U x = connectedComponentIn U z := connectedComponentIn_eq hz2
    have hsame : connectedComponentIn U y = connectedComponentIn U x := e1.trans e2.symm
    rw [← hsame]
    exact mem_connectedComponentIn hyU
  rw [← heq]
  exact hK.inter_right isClosed_closure

/-- Hence it is confined to a closed interval lying inside the component. -/
theorem exists_Icc_inside {U K : Set ℝ} (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    {x : ℝ} (hx : x ∈ U) (hne : (K ∩ connectedComponentIn U x).Nonempty) :
    ∃ c d : ℝ, K ∩ connectedComponentIn U x ⊆ Set.Icc c d ∧
      Set.Icc c d ⊆ connectedComponentIn U x := by
  have hcpt := compact_inter_comp hU hKU hK hx
  have hc := hcpt.sInf_mem hne
  have hd := hcpt.sSup_mem hne
  have hord : (connectedComponentIn U x).OrdConnected :=
    (isPreconnected_connectedComponentIn).ordConnected
  refine ⟨sInf (K ∩ connectedComponentIn U x), sSup (K ∩ connectedComponentIn U x), ?_, ?_⟩
  · intro y hy
    exact ⟨csInf_le hcpt.bddBelow hy, le_csSup hcpt.bddAbove hy⟩
  · exact fun y hy => hord.out hc.2 hd.2 hy

end BS_32b

namespace BS_32c
open BrinSquier

lemma inv_fixes_compl {U : Set ℝ} {w : ℝ ≃o ℝ} (hwU : ∀ y, y ∉ U → w y = y) :
    ∀ y, y ∉ U → w⁻¹ y = y := fun y hy =>
  w.injective (by rw [RelIso.apply_inv_self, hwU y hy])

lemma mem_supp_apply {w : ℝ ≃o ℝ} {x : ℝ} (hx : x ∈ supp w) : w x ∈ supp w :=
  fun h => hx (w.injective h)

lemma pres_comp {U : Set ℝ} {h : ℝ ≃o ℝ} (hh : ∀ y, y ∉ U → h y = y) {x₀ : ℝ}
    {x : ℝ} (hx : x ∈ connectedComponentIn U x₀) : h x ∈ connectedComponentIn U x₀ := by
  have h1 := HomeoLine.mem_connectedComponentIn_of_fixes_compl hh
    ((connectedComponentIn_subset U x₀) hx)
  rwa [← connectedComponentIn_eq hx] at h1

/-- Two maps supported in `U` whose moved sets are disjoint inside one component of `U`
have commutator equal to the identity on that component. -/
theorem commutator_id_on_comp {U : Set ℝ} {w w' : ℝ ≃o ℝ} {x₀ : ℝ}
    (hwU : ∀ y, y ∉ U → w y = y) (hw'U : ∀ y, y ∉ U → w' y = y)
    (hdisj : ∀ x ∈ connectedComponentIn U x₀, x ∉ supp w ∨ x ∉ supp w') :
    ∀ x ∈ connectedComponentIn U x₀, (w * w' * w⁻¹ * w'⁻¹) x = x := by
  have stepA : ∀ x ∈ connectedComponentIn U x₀, w (w' x) = w' (w x) := by
    intro x hx
    by_cases hxw : x ∈ supp w
    · have hxw' : x ∉ supp w' := by
        rcases hdisj x hx with h | h
        · exact absurd hxw h
        · exact h
      have h2 : w x ∉ supp w' := by
        rcases hdisj (w x) (pres_comp hwU hx) with h | h
        · exact absurd (mem_supp_apply hxw) h
        · exact h
      simp only [not_not.1 hxw', not_not.1 h2]
    · by_cases hxw' : x ∈ supp w'
      · have h2 : w' x ∉ supp w := by
          rcases hdisj (w' x) (pres_comp hw'U hx) with h | h
          · exact h
          · exact absurd (mem_supp_apply hxw') h
        simp only [not_not.1 hxw, not_not.1 h2]
      · simp only [not_not.1 hxw, not_not.1 hxw']
  intro x hx
  show w (w' (w⁻¹ (w'⁻¹ x))) = x
  have hxi : w'⁻¹ x ∈ connectedComponentIn U x₀ := pres_comp (inv_fixes_compl hw'U) hx
  have hxii : w⁻¹ (w'⁻¹ x) ∈ connectedComponentIn U x₀ :=
    pres_comp (inv_fixes_compl hwU) hxi
  rw [stepA _ hxii, RelIso.apply_inv_self, RelIso.apply_inv_self]

end BS_32c

namespace BS_32d
open BrinSquier BS_32c

/-- Conjugating by a map that pushes `[c,d]` past `d` makes the moved sets disjoint
inside the component. -/
theorem disjoint_in_comp {U : Set ℝ} {w z : ℝ ≃o ℝ} {x₀ c d : ℝ}
    (hzU : ∀ y, y ∉ U → z y = y)
    (hsub : supp w ∩ connectedComponentIn U x₀ ⊆ Set.Icc c d)
    (hzc : d < z c) :
    ∀ x ∈ connectedComponentIn U x₀, x ∉ supp w ∨ x ∉ supp (z * w * z⁻¹) := by
  intro x hx
  by_cases h1 : x ∈ supp w
  · refine Or.inr fun h2 => ?_
    rw [BrinSquier.supp_conj z w] at h2
    obtain ⟨y, hy, hxy⟩ := h2
    have hyC : y ∈ connectedComponentIn U x₀ := by
      have h3 : z⁻¹ x ∈ connectedComponentIn U x₀ := pres_comp (inv_fixes_compl hzU) hx
      rwa [← hxy, RelIso.inv_apply_self] at h3
    have hy2 := hsub ⟨hy, hyC⟩
    have hx2 := hsub ⟨h1, hx⟩
    have hmono : z c ≤ z y := z.monotone hy2.1
    rw [hxy] at hmono
    linarith [hx2.2]
  · exact Or.inl h1

/-- A conjugate meets no component that the original misses. -/
theorem met_conj_subset {U : Set ℝ} {w z : ℝ ≃o ℝ} (hzU : ∀ y, y ∉ U → z y = y)
    {x₀ : ℝ} (h : (supp (z * w * z⁻¹) ∩ connectedComponentIn U x₀).Nonempty) :
    (supp w ∩ connectedComponentIn U x₀).Nonempty := by
  obtain ⟨x, hx1, hx2⟩ := h
  rw [BrinSquier.supp_conj z w] at hx1
  obtain ⟨y, hy, hxy⟩ := hx1
  refine ⟨y, hy, ?_⟩
  have h3 : z⁻¹ x ∈ connectedComponentIn U x₀ := pres_comp (inv_fixes_compl hzU) hx2
  rwa [← hxy, RelIso.inv_apply_self] at h3

/-- Every element of `⟨f, g⟩` fixes everything outside `supp f ∪ supp g`. -/
theorem closure_fixes_compl {f g : ℝ ≃o ℝ} :
    ∀ w ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)),
      ∀ y, y ∉ supp f ∪ supp g → w y = y := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      intro y hy
      rcases hx with rfl | rfl
      · exact not_not.1 (fun h => hy (Or.inl h))
      · exact not_not.1 (fun h => hy (Or.inr h))
  | one => intro y _; rfl
  | mul a b _ _ ha hb => intro y hy; show a (b y) = y; rw [hb y hy, ha y hy]
  | inv a _ ha => intro y hy; exact inv_fixes_compl (U := supp f ∪ supp g) ha y hy

end BS_32d

namespace BS_final
open BrinSquier BS_32 BS_32b BS_32c BS_32d

theorem supp_mul_subset (f g : ℝ ≃o ℝ) : supp (f * g) ⊆ supp f ∪ supp g := by
  intro x hx
  by_contra hc
  simp only [Set.mem_union, not_or] at hc
  exact hx (by show f (g x) = x; rw [not_not.1 hc.2, not_not.1 hc.1])

theorem supp_inv (f : ℝ ≃o ℝ) : supp f⁻¹ = supp f := by
  ext x
  constructor
  · intro hx hc
    apply hx
    have h1 := RelIso.inv_apply_self f x
    rw [hc] at h1
    exact h1
  · intro hx hc
    apply hx
    have h1 := RelIso.apply_inv_self f x
    rw [hc] at h1
    exact h1

lemma supp_commutator_subset (a b : ℝ ≃o ℝ) :
    supp (a * b * a⁻¹ * b⁻¹) ⊆ supp a ∪ supp b := by
  have h1 := supp_mul_subset (a * b * a⁻¹) b⁻¹
  have h2 := supp_mul_subset (a * b) a⁻¹
  have h3 := supp_mul_subset a b
  intro x hx
  rcases h1 hx with h | h
  · rcases h2 h with h' | h'
    · exact h3 h'
    · exact Or.inl (by rwa [supp_inv] at h')
  · exact Or.inr (by rwa [supp_inv] at h)

lemma maps_into_of_fixes_compl {U : Set ℝ} {z : ℝ ≃o ℝ} (hz : ∀ y, y ∉ U → z y = y)
    {y : ℝ} (hy : y ∈ U) : z y ∈ U := by
  by_contra hc
  have h2 : z y = y := z.injective (hz (z y) hc)
  rw [h2] at hc
  exact hc hy

lemma supp_eq_empty_iff {w : ℝ ≃o ℝ} (h : supp w = ∅) : w = 1 :=
  RelIso.ext fun x => not_not.1 fun hx => (Set.eq_empty_iff_forall_notMem.mp h x) hx

end BS_final

namespace BS_fin2
open BrinSquier BS_32 BS_32b BS_32c BS_32d BS_final

lemma zpow_fix {v : ℝ ≃o ℝ} {x : ℝ} (h : v x = x) : ∀ k : ℤ, (v ^ k) x = x := by
  have hinv : v⁻¹ x = x := v.injective (by rw [RelIso.apply_inv_self, h])
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add v (n : ℤ) 1, zpow_one]; show (v ^ (n : ℤ)) (v x) = x; rw [h, ih]
  | pred n ih =>
      rw [show (-(n : ℤ) - 1) = (-(n : ℤ)) + (-1) by ring, zpow_add v (-(n : ℤ)) (-1),
        zpow_neg_one]
      show (v ^ (-(n : ℤ))) (v⁻¹ x) = x
      rw [hinv, ih]

lemma zpow_fixes_compl {U : Set ℝ} {h : ℝ ≃o ℝ} (hh : ∀ y, y ∉ U → h y = y) (k : ℤ) :
    ∀ y, y ∉ U → (h ^ k) y = y := fun y hy => zpow_fix (hh y hy) k

lemma mem_supp_zpow {v : ℝ ≃o ℝ} {x : ℝ} (hx : x ∈ supp v) (k : ℤ) : (v ^ k) x ∈ supp v := by
  intro hcon
  apply hx
  have h1 : (v ^ (-k)) ((v ^ k) x) = x := by
    show (v ^ (-k) * v ^ k) x = x; rw [← zpow_add]; simp
  rw [zpow_fix hcon (-k)] at h1
  rw [← h1]
  exact hcon

end BS_fin2


namespace BS_inf
open BrinSquier BS_32 BS_32b BS_32c BS_32d BS_final BS_fin2

/-- An open interval strictly containing a compact interval inside an order-connected set. -/
lemma exists_open_enlargement {C : Set ℝ} (hCopen : IsOpen C) (hCord : C.OrdConnected)
    {c d : ℝ} (hcd : c ≤ d) (hc : c ∈ C) (hd : d ∈ C) :
    ∃ c' d' : ℝ, c' < c ∧ d < d' ∧ Set.Icc c' d' ⊆ C := by
  obtain ⟨e1, he1, h1⟩ := Metric.isOpen_iff.mp hCopen c hc
  obtain ⟨e2, he2, h2⟩ := Metric.isOpen_iff.mp hCopen d hd
  refine ⟨c - e1/2, d + e2/2, by linarith, by linarith, ?_⟩
  have hc' : c - e1/2 ∈ C := h1 (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hd' : d + e2/2 ∈ C := h2 (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  exact fun y hy => hCord.out hc' hd' hy

/-- A map supported in `U` with moved set confined to `S` inside a component carries `S`
into itself, and so does every integer power of it. -/
lemma zpow_mapsTo_of_supp_subset {U S : Set ℝ} {v : ℝ ≃o ℝ} {x₀ : ℝ}
    (hvU : ∀ y, y ∉ U → v y = y)
    (hS : S ⊆ connectedComponentIn U x₀)
    (hsub : supp v ∩ connectedComponentIn U x₀ ⊆ S) :
    ∀ k : ℤ, ∀ y ∈ S, (v ^ k) y ∈ S := by
  have h1 : ∀ y ∈ S, v y ∈ S := by
    intro y hy
    by_cases h : y ∈ supp v
    · exact hsub ⟨mem_supp_apply h, pres_comp hvU (hS hy)⟩
    · rw [not_not.1 h]; exact hy
  have h2 : ∀ y ∈ S, v⁻¹ y ∈ S := by
    intro y hy
    by_cases h : y ∈ supp v⁻¹
    · refine hsub ⟨?_, pres_comp (inv_fixes_compl hvU) (hS hy)⟩
      have h3 := mem_supp_apply h
      rwa [supp_inv] at h3
    · rw [not_not.1 h]; exact hy
  intro k
  induction k using Int.induction_on with
  | zero => intro y hy; rw [zpow_zero]; exact hy
  | succ n ih =>
      intro y hy
      have e : (v ^ ((n : ℤ) + 1)) y = (v ^ (n : ℤ)) (v y) := by rw [zpow_add_one]; rfl
      rw [e]; exact ih _ (h1 y hy)
  | pred n ih =>
      intro y hy
      have e : (v ^ (-(n : ℤ) - 1)) y = (v ^ (-(n : ℤ))) (v⁻¹ y) := by rw [zpow_sub_one]; rfl
      rw [e]; exact ih _ (h2 y hy)

/-- Independence of a family by point evaluation: each index owns a region that the other
members fix pointwise, that its own powers preserve, and in which one point is moved by
every nonzero power. -/
lemma free_of_owned_regions {x : ℤ → ℝ ≃o ℝ} {I : ℤ → Set ℝ}
    (hfix : ∀ m n : ℤ, m ≠ n → ∀ y ∈ I m, ∀ k : ℤ, (x n ^ k) y = y)
    (hmaps : ∀ m : ℤ, ∀ k : ℤ, ∀ y ∈ I m, (x m ^ k) y ∈ I m)
    (hmove : ∀ m : ℤ, ∃ y ∈ I m, ∀ k : ℤ, k ≠ 0 → (x m ^ k) y ≠ y) :
    ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
      (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  intro l hl n hprod m hm
  by_contra hn0
  obtain ⟨p, hpI, hpmove⟩ := hmove m
  have claimA : ∀ l' : List ℤ, m ∉ l' →
      ∀ y ∈ I m, (l'.map (fun j => x j ^ n j)).prod y = y := by
    intro l'
    induction l' with
    | nil => intro _ y _; rfl
    | cons j t ih =>
        intro hmt y hy
        have hj : m ≠ j := by rintro rfl; exact hmt (by simp)
        have e : ((j :: t).map (fun j => x j ^ n j)).prod y
            = (x j ^ n j) ((t.map (fun j => x j ^ n j)).prod y) := by
          simp only [List.map_cons, List.prod_cons]; rfl
        rw [e, ih (fun h => hmt (List.mem_cons_of_mem _ h)) y hy]
        exact hfix m j hj y hy (n j)
  have claimB : ∀ l' : List ℤ, l'.Nodup → m ∈ l' →
      ∀ y ∈ I m, (l'.map (fun j => x j ^ n j)).prod y = (x m ^ n m) y := by
    intro l'
    induction l' with
    | nil => intro _ h; simp at h
    | cons j t ih =>
        intro hnd hmem y hy
        have e : ((j :: t).map (fun j => x j ^ n j)).prod y
            = (x j ^ n j) ((t.map (fun j => x j ^ n j)).prod y) := by
          simp only [List.map_cons, List.prod_cons]; rfl
        rw [e]
        rcases eq_or_ne j m with rfl | hjm
        · rw [claimA t (List.nodup_cons.mp hnd).1 y hy]
        · have hmt : m ∈ t := by
            rcases List.mem_cons.mp hmem with h | h
            · exact absurd h.symm hjm
            · exact h
          rw [ih (List.nodup_cons.mp hnd).2 hmt y hy]
          exact hfix m j (Ne.symm hjm) _ (hmaps m (n m) y hy) (n j)
  have hev := claimB l hl hm p hpI
  rw [hprod] at hev
  exact hpmove (n m) hn0 hev.symm

end BS_inf

open BrinSquier BS_32 BS_32b BS_32c BS_32d BS_final BS_fin2 BS_inf in
theorem solution (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ x : ℤ → ℝ ≃o ℝ, (∀ m, x m ∈ G) ∧ (∀ p q : ℤ, x p * x q = x q * x p) ∧
      ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
        (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  classical
  push_neg at hne
  obtain ⟨f, hf, g, hg, hfg⟩ := hne
  obtain ⟨hfPLF, hfb, hft⟩ := hG f hf
  obtain ⟨hgPLF, hgb, hgt⟩ := hG g hg
  have hfK : f ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) := Subgroup.subset_closure (by simp)
  have hgK : g ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) := Subgroup.subset_closure (by simp)
  have hKG : Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) ≤ G := by
    rw [Subgroup.closure_le]; rintro y (rfl | rfl) <;> assumption
  have hUopen : IsOpen (supp f ∪ supp g) := (isOpen_supp f).union (isOpen_supp g)
  have hne1 : f * g * f⁻¹ * g⁻¹ ≠ 1 := by
    intro h; apply hfg
    calc f * g = (f * g * f⁻¹ * g⁻¹) * (g * f) := by group
      _ = g * f := by rw [h, one_mul]
  set W : Set (ℝ ≃o ℝ) :=
    {v | v ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) ∧ v ≠ 1 ∧
      IsCompact (closure (supp v)) ∧ closure (supp v) ⊆ supp f ∪ supp g} with hWdef
  have hw1W : f * g * f⁻¹ * g⁻¹ ∈ W :=
    ⟨mul_mem (mul_mem (mul_mem hfK hgK) (inv_mem hfK)) (inv_mem hgK), hne1,
     BrinSquier.compact_closure_supp_commutator hfb hft hgb hgt,
     BrinSquier.closure_supp_commutator_subset hfPLF hgPLF⟩
  have hSne : {k : ℕ | ∃ v ∈ W, (Met (supp f ∪ supp g) v).ncard = k}.Nonempty := ⟨_, _, hw1W, rfl⟩
  obtain ⟨w, hwW, hwN⟩ := Nat.sInf_mem hSne
  have hmin : ∀ v ∈ W,
      sInf {k : ℕ | ∃ v ∈ W, (Met (supp f ∪ supp g) v).ncard = k}
        ≤ (Met (supp f ∪ supp g) v).ncard := fun v hv => Nat.sInf_le ⟨v, hv, rfl⟩
  have hsuppne : (supp w).Nonempty := by
    rcases Set.eq_empty_or_nonempty (supp w) with h | h
    · exact absurd (supp_eq_empty_iff h) hwW.2.1
    · exact h
  obtain ⟨x₀, hx₀⟩ := hsuppne
  have hx₀U : x₀ ∈ supp f ∪ supp g := hwW.2.2.2 (subset_closure hx₀)
  obtain ⟨c, d, hcd1, hcd2⟩ := exists_Icc_inside hUopen hwW.2.2.2 hwW.2.2.1 hx₀U
    ⟨x₀, subset_closure hx₀, mem_connectedComponentIn hx₀U⟩
  have hsw : supp w ∩ connectedComponentIn (supp f ∪ supp g) x₀ ⊆ Set.Icc c d :=
    fun y hy => hcd1 ⟨subset_closure hy.1, hy.2⟩
  have hx₀Icc : x₀ ∈ Set.Icc c d := hsw ⟨hx₀, mem_connectedComponentIn hx₀U⟩
  have hcdle : c ≤ d := le_trans hx₀Icc.1 hx₀Icc.2
  have hcC : c ∈ connectedComponentIn (supp f ∪ supp g) x₀ := hcd2 ⟨le_refl _, hcdle⟩
  have hdC : d ∈ connectedComponentIn (supp f ∪ supp g) x₀ := hcd2 ⟨hcdle, le_refl _⟩
  obtain ⟨c', d', hc'c, hdd', hIcc'⟩ := exists_open_enlargement
    (hUopen.connectedComponentIn) (isPreconnected_connectedComponentIn.ordConnected)
    hcdle hcC hdC
  have hc'd'le : c' ≤ d' := by linarith
  obtain ⟨z, hzK, hzc⟩ := HomeoLine.exists_mem_closure_apply_gt f g (fun t ht => by
    rcases (connectedComponentIn_subset (supp f ∪ supp g) x₀) (hIcc' ht) with h | h
    · exact Or.inl h
    · exact Or.inr h)
  have hzcheck : d' < z c' := hzc
  have hzfix := closure_fixes_compl z hzK
  have hwfix := closure_fixes_compl w hwW.1
  -- Minimality of the component count forces the commutator with any suitable conjugate
  -- of `w` to be trivial.  This is the paper's p. 495 step, with the conjugator left free.
  have hc1 : ∀ y ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)), d < y c →
      w * (y * w * y⁻¹) * w⁻¹ * (y * w * y⁻¹)⁻¹ = 1 := by
    intro y hyK hyc
    have hyfix := closure_fixes_compl y hyK
    have hw'K : y * w * y⁻¹ ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) :=
      mul_mem (mul_mem hyK hwW.1) (inv_mem hyK)
    have hw'fix := closure_fixes_compl (y * w * y⁻¹) hw'K
    have hdisj := disjoint_in_comp hyfix hsw hyc
    have hcommC := commutator_id_on_comp hwfix hw'fix hdisj
    by_contra hc
    have hsuppsub := supp_commutator_subset w (y * w * y⁻¹)
    have hconjcpt : IsCompact (y '' closure (supp w)) :=
      hwW.2.2.1.image (OrderIso.continuous y)
    have hclos' : closure (supp (y * w * y⁻¹)) ⊆ y '' closure (supp w) :=
      closure_minimal (by rw [BrinSquier.supp_conj y w]; exact Set.image_mono subset_closure)
        hconjcpt.isClosed
    have hbig : IsCompact (closure (supp w) ∪ y '' closure (supp w)) :=
      hwW.2.2.1.union hconjcpt
    have hcsub : closure (supp (w * (y * w * y⁻¹) * w⁻¹ * (y * w * y⁻¹)⁻¹))
        ⊆ closure (supp w) ∪ y '' closure (supp w) :=
      closure_minimal (fun t ht => by
        rcases hsuppsub ht with h | h
        · exact Or.inl (subset_closure h)
        · exact Or.inr (hclos' (subset_closure h))) hbig.isClosed
    have hinW : w * (y * w * y⁻¹) * w⁻¹ * (y * w * y⁻¹)⁻¹ ∈ W :=
      ⟨mul_mem (mul_mem (mul_mem hwW.1 hw'K) (inv_mem hwW.1)) (inv_mem hw'K), hc,
       hbig.of_isClosed_subset isClosed_closure hcsub,
       hcsub.trans (Set.union_subset hwW.2.2.2 (fun t ht => by
         obtain ⟨s, hs, rfl⟩ := ht
         exact maps_into_of_fixes_compl hyfix (hwW.2.2.2 hs)))⟩
    have hCin : connectedComponentIn (supp f ∪ supp g) x₀ ∈ Met (supp f ∪ supp g) w :=
      ⟨⟨x₀, hx₀U, rfl⟩, ⟨x₀, hx₀, mem_connectedComponentIn hx₀U⟩⟩
    have hMetsub : Met (supp f ∪ supp g) (w * (y * w * y⁻¹) * w⁻¹ * (y * w * y⁻¹)⁻¹)
        ⊆ Met (supp f ∪ supp g) w \ {connectedComponentIn (supp f ∪ supp g) x₀} := by
      rintro C ⟨⟨t, htU, rfl⟩, hCne⟩
      refine ⟨⟨⟨t, htU, rfl⟩, ?_⟩, ?_⟩
      · obtain ⟨s, hs1, hs2⟩ := hCne
        rcases hsuppsub hs1 with h | h
        · exact ⟨s, h, hs2⟩
        · exact met_conj_subset hyfix ⟨s, h, hs2⟩
      · intro hCeq
        rw [Set.mem_singleton_iff] at hCeq
        obtain ⟨s, hs1, hs2⟩ := hCne
        rw [hCeq] at hs2
        exact hs1 (hcommC s hs2)
    have hlt : (Met (supp f ∪ supp g) (w * (y * w * y⁻¹) * w⁻¹ * (y * w * y⁻¹)⁻¹)).ncard
        < (Met (supp f ∪ supp g) w).ncard := by
      refine Set.ncard_lt_ncard ⟨hMetsub.trans Set.sdiff_subset, fun hcon => ?_⟩
        (met_finite hfPLF hgPLF w)
      exact (hMetsub (hcon hCin)).2 rfl
    have hge := hmin _ hinW
    rw [hwN] at hlt
    omega
  -- positive powers of `z` also push `c` past `d`
  have hstep : ∀ k : ℕ, (z ^ (k : ℤ)) c' ≤ (z ^ ((k : ℤ) + 1)) c' := by
    intro k
    have e : (z ^ ((k : ℤ) + 1)) c' = (z ^ (k : ℤ)) (z c') := by rw [zpow_add_one]; rfl
    rw [e]
    exact (z ^ (k : ℤ)).monotone (by linarith)
  have hmono : Monotone (fun k : ℕ => (z ^ (k : ℤ)) c') := monotone_nat_of_le_succ hstep
  have hpos : ∀ p : ℤ, 0 < p → d < (z ^ p) c := by
    intro p hp
    have h2 : (z ^ ((1 : ℕ) : ℤ)) c' ≤ (z ^ ((p.toNat : ℕ) : ℤ)) c' := hmono (by omega)
    rw [show ((1 : ℕ) : ℤ) = 1 from rfl, zpow_one,
      show ((p.toNat : ℕ) : ℤ) = p from Int.toNat_of_nonneg (le_of_lt hp)] at h2
    have h5 : (z ^ p) c' < (z ^ p) c := (z ^ p).lt_iff_lt.2 hc'c
    linarith
  -- the conjugates of `w` by powers of `z` commute pairwise
  have hcommz : ∀ p : ℤ, p ≠ 0 →
      w * (z ^ p * w * (z ^ p)⁻¹) = (z ^ p * w * (z ^ p)⁻¹) * w := by
    have key : ∀ p : ℤ, 0 < p →
        w * (z ^ p * w * (z ^ p)⁻¹) = (z ^ p * w * (z ^ p)⁻¹) * w := by
      intro p hp
      have h0 := hc1 (z ^ p) (Subgroup.zpow_mem _ hzK p) (hpos p hp)
      calc w * (z ^ p * w * (z ^ p)⁻¹)
          = (w * (z ^ p * w * (z ^ p)⁻¹) * w⁻¹ * (z ^ p * w * (z ^ p)⁻¹)⁻¹)
              * ((z ^ p * w * (z ^ p)⁻¹) * w) := by group
        _ = (z ^ p * w * (z ^ p)⁻¹) * w := by rw [h0, one_mul]
    intro p hp
    rcases lt_or_gt_of_ne hp with hneg | hp'
    · have h := key (-p) (by omega)
      have e : z ^ p = (z ^ (-p))⁻¹ := by simp [zpow_neg]
      rw [e]
      calc w * ((z ^ (-p))⁻¹ * w * ((z ^ (-p))⁻¹)⁻¹)
          = (z ^ (-p))⁻¹ * ((z ^ (-p) * w * (z ^ (-p))⁻¹) * w) * (z ^ (-p)) := by group
        _ = (z ^ (-p))⁻¹ * (w * (z ^ (-p) * w * (z ^ (-p))⁻¹)) * (z ^ (-p)) := by rw [h]
        _ = ((z ^ (-p))⁻¹ * w * ((z ^ (-p))⁻¹)⁻¹) * w := by group
    · exact key p hp'
  have hxK : ∀ m : ℤ, z ^ m * w * (z ^ m)⁻¹ ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) :=
    fun m => mul_mem (mul_mem (Subgroup.zpow_mem _ hzK m) hwW.1)
      (inv_mem (Subgroup.zpow_mem _ hzK m))
  -- the owned intervals
  have hIsubC : ∀ m : ℤ, Set.Ioo ((z ^ m) c') ((z ^ m) d') ⊆
      connectedComponentIn (supp f ∪ supp g) x₀ := by
    intro m y hy
    have h1 : (z ^ m)⁻¹ y ∈ Set.Icc c' d' := by
      constructor
      · have h2 := ((z ^ m)⁻¹).lt_iff_lt.2 hy.1
        rw [RelIso.inv_apply_self] at h2
        exact le_of_lt h2
      · have h2 := ((z ^ m)⁻¹).lt_iff_lt.2 hy.2
        rw [RelIso.inv_apply_self] at h2
        exact le_of_lt h2
    have h4 := pres_comp (zpow_fixes_compl hzfix m) (hIcc' h1)
    rwa [RelIso.apply_inv_self] at h4
  have hsuppx : ∀ m : ℤ, supp (z ^ m * w * (z ^ m)⁻¹) ∩
      connectedComponentIn (supp f ∪ supp g) x₀ ⊆ Set.Ioo ((z ^ m) c') ((z ^ m) d') := by
    intro m y hy
    obtain ⟨hy1, hyC⟩ := hy
    rw [BrinSquier.supp_conj (z ^ m) w] at hy1
    obtain ⟨u, hu, huy⟩ := hy1
    have h1 : (z ^ m)⁻¹ y ∈ connectedComponentIn (supp f ∪ supp g) x₀ :=
      pres_comp (inv_fixes_compl (zpow_fixes_compl hzfix m)) hyC
    rw [← huy, RelIso.inv_apply_self] at h1
    have h2 := hsw ⟨hu, h1⟩
    rw [← huy]
    exact ⟨(z ^ m).lt_iff_lt.2 (lt_of_lt_of_le hc'c h2.1),
           (z ^ m).lt_iff_lt.2 (lt_of_le_of_lt h2.2 hdd')⟩
  refine ⟨fun m => z ^ m * w * (z ^ m)⁻¹, fun m => hKG (hxK m), ?_, ?_⟩
  · -- pairwise commuting
    intro p q
    rcases eq_or_ne p q with rfl | hpq
    · rfl
    · have h := hcommz (q - p) (sub_ne_zero.2 (Ne.symm hpq))
      have e : z ^ q = z ^ p * z ^ (q - p) := by
        rw [← zpow_add]; congr 1; ring
      show z ^ p * w * (z ^ p)⁻¹ * (z ^ q * w * (z ^ q)⁻¹)
          = z ^ q * w * (z ^ q)⁻¹ * (z ^ p * w * (z ^ p)⁻¹)
      rw [e]
      calc z ^ p * w * (z ^ p)⁻¹ * (z ^ p * z ^ (q - p) * w * (z ^ p * z ^ (q - p))⁻¹)
          = z ^ p * (w * (z ^ (q - p) * w * (z ^ (q - p))⁻¹)) * (z ^ p)⁻¹ := by group
        _ = z ^ p * ((z ^ (q - p) * w * (z ^ (q - p))⁻¹) * w) * (z ^ p)⁻¹ := by rw [h]
        _ = z ^ p * z ^ (q - p) * w * (z ^ p * z ^ (q - p))⁻¹ * (z ^ p * w * (z ^ p)⁻¹) := by
              group
  · -- independence, by point evaluation in the owned intervals
    refine free_of_owned_regions (I := fun m => Set.Ioo ((z ^ m) c') ((z ^ m) d')) ?_ ?_ ?_
    · intro m n hmn y hy k
      refine zpow_fix ?_ k
      by_contra hcon
      have h1 : y ∈ supp (z ^ n * w * (z ^ n)⁻¹) := hcon
      have h2 := hsuppx n ⟨h1, hIsubC m hy⟩
      exact Set.disjoint_left.mp
        (HomeoLine.pairwise_disjoint_zpow_image hc'd'le hzcheck n m (Ne.symm hmn)) h2 hy
    · intro m
      exact zpow_mapsTo_of_supp_subset (closure_fixes_compl _ (hxK m)) (hIsubC m) (hsuppx m)
    · intro m
      refine ⟨(z ^ m) x₀, ?_, ?_⟩
      · have h2 := hsw ⟨hx₀, mem_connectedComponentIn hx₀U⟩
        exact ⟨(z ^ m).lt_iff_lt.2 (lt_of_lt_of_le hc'c h2.1),
               (z ^ m).lt_iff_lt.2 (lt_of_le_of_lt h2.2 hdd')⟩
      · intro k hk
        refine HomeoLine.zpow_moves_of_moves ?_ k hk
        have h3 : (z ^ m) x₀ ∈ supp (z ^ m * w * (z ^ m)⁻¹) := by
          rw [BrinSquier.supp_conj (z ^ m) w]; exact ⟨x₀, hx₀, rfl⟩
        exact h3
