-- Prove2me | solution 1 for BrinSquier.zsq_of_not_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:59:20.709035+00:00
-- url     : https://prove2.me/submissions/3817813d-56fe-41b9-aeec-77d3fb112d2b

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

open BrinSquier BS_32 BS_32b BS_32c BS_32d BS_final BS_fin2 in
theorem solution (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ u ∈ G, ∃ v ∈ G, u * v = v * u ∧
      Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  classical
  push_neg at hne
  obtain ⟨f, hf, g, hg, hfg⟩ := hne
  obtain ⟨hfPLF, hfb, hft⟩ := hG f hf
  obtain ⟨hgPLF, hgb, hgt⟩ := hG g hg
  have hfK : f ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) := Subgroup.subset_closure (by simp)
  have hgK : g ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) := Subgroup.subset_closure (by simp)
  have hKG : Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) ≤ G := by
    rw [Subgroup.closure_le]; rintro x (rfl | rfl) <;> assumption
  have hUopen : IsOpen (supp f ∪ supp g) := (isOpen_supp f).union (isOpen_supp g)
  have hne1 : f * g * f⁻¹ * g⁻¹ ≠ 1 := by
    intro h
    apply hfg
    calc f * g = (f * g * f⁻¹ * g⁻¹) * (g * f) := by group
      _ = g * f := by rw [h, one_mul]
  set W : Set (ℝ ≃o ℝ) :=
    {w | w ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) ∧ w ≠ 1 ∧
      IsCompact (closure (supp w)) ∧ closure (supp w) ⊆ supp f ∪ supp g} with hWdef
  have hw1W : f * g * f⁻¹ * g⁻¹ ∈ W :=
    ⟨mul_mem (mul_mem (mul_mem hfK hgK) (inv_mem hfK)) (inv_mem hgK), hne1,
     BrinSquier.compact_closure_supp_commutator hfb hft hgb hgt,
     BrinSquier.closure_supp_commutator_subset hfPLF hgPLF⟩
  -- minimize the number of components met
  have hSne : {n : ℕ | ∃ w ∈ W, (Met (supp f ∪ supp g) w).ncard = n}.Nonempty :=
    ⟨_, _, hw1W, rfl⟩
  obtain ⟨w, hwW, hwN⟩ := Nat.sInf_mem hSne
  have hmin : ∀ v ∈ W,
      sInf {n : ℕ | ∃ w ∈ W, (Met (supp f ∪ supp g) w).ncard = n}
        ≤ (Met (supp f ∪ supp g) v).ncard := fun v hv => Nat.sInf_le ⟨v, hv, rfl⟩
  -- a component `w` meets, and a closed interval confining it there
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
  -- (3.5) supplies a word pushing `[c,d]` past `d`
  obtain ⟨z, hzK, hzc⟩ := HomeoLine.exists_mem_closure_apply_gt f g (fun t ht => by
    rcases (connectedComponentIn_subset (supp f ∪ supp g) x₀) (hcd2 ht) with h | h
    · exact Or.inl h
    · exact Or.inr h)
  have hzfix := closure_fixes_compl z hzK
  have hwfix := closure_fixes_compl w hwW.1
  have hw'K : z * w * z⁻¹ ∈ Subgroup.closure ({f, g} : Set (ℝ ≃o ℝ)) :=
    mul_mem (mul_mem hzK hwW.1) (inv_mem hzK)
  have hw'fix := closure_fixes_compl (z * w * z⁻¹) hw'K
  have hdisj := disjoint_in_comp hzfix hsw hzc
  have hcommC := commutator_id_on_comp hwfix hw'fix hdisj
  -- minimality forces the commutator to be trivial
  have hc1 : w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹ = 1 := by
    by_contra hc
    have hsuppsub := supp_commutator_subset w (z * w * z⁻¹)
    have hconjcpt : IsCompact (z '' closure (supp w)) :=
      hwW.2.2.1.image (OrderIso.continuous z)
    have hclos' : closure (supp (z * w * z⁻¹)) ⊆ z '' closure (supp w) :=
      closure_minimal (by rw [BrinSquier.supp_conj z w]; exact Set.image_mono subset_closure)
        hconjcpt.isClosed
    have hbig : IsCompact (closure (supp w) ∪ z '' closure (supp w)) :=
      hwW.2.2.1.union hconjcpt
    have hcsub : closure (supp (w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹))
        ⊆ closure (supp w) ∪ z '' closure (supp w) :=
      closure_minimal (fun x hx => by
        rcases hsuppsub hx with h | h
        · exact Or.inl (subset_closure h)
        · exact Or.inr (hclos' (subset_closure h))) hbig.isClosed
    have hinW : w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹ ∈ W :=
      ⟨mul_mem (mul_mem (mul_mem hwW.1 hw'K) (inv_mem hwW.1)) (inv_mem hw'K), hc,
       hbig.of_isClosed_subset isClosed_closure hcsub,
       hcsub.trans (Set.union_subset hwW.2.2.2 (fun y hy => by
         obtain ⟨t, ht, rfl⟩ := hy
         exact maps_into_of_fixes_compl hzfix (hwW.2.2.2 ht)))⟩
    have hCin : connectedComponentIn (supp f ∪ supp g) x₀ ∈ Met (supp f ∪ supp g) w :=
      ⟨⟨x₀, hx₀U, rfl⟩, ⟨x₀, hx₀, mem_connectedComponentIn hx₀U⟩⟩
    have hMetsub : Met (supp f ∪ supp g) (w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹)
        ⊆ Met (supp f ∪ supp g) w \ {connectedComponentIn (supp f ∪ supp g) x₀} := by
      rintro C ⟨⟨y, hyU, rfl⟩, hCne⟩
      refine ⟨⟨⟨y, hyU, rfl⟩, ?_⟩, ?_⟩
      · obtain ⟨x, hx1, hx2⟩ := hCne
        rcases hsuppsub hx1 with h | h
        · exact ⟨x, h, hx2⟩
        · exact met_conj_subset hzfix ⟨x, h, hx2⟩
      · intro hCeq
        rw [Set.mem_singleton_iff] at hCeq
        obtain ⟨x, hx1, hx2⟩ := hCne
        rw [hCeq] at hx2
        exact hx1 (hcommC x hx2)
    have hlt : (Met (supp f ∪ supp g) (w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹)).ncard
        < (Met (supp f ∪ supp g) w).ncard := by
      refine Set.ncard_lt_ncard ⟨hMetsub.trans Set.sdiff_subset, fun hcon => ?_⟩
        (met_finite hfPLF hgPLF w)
      exact (hMetsub (hcon hCin)).2 rfl
    have := hmin _ hinW
    rw [hwN] at hlt
    omega
  have hcomm : w * (z * w * z⁻¹) = (z * w * z⁻¹) * w := by
    calc w * (z * w * z⁻¹)
        = (w * (z * w * z⁻¹) * w⁻¹ * (z * w * z⁻¹)⁻¹) * ((z * w * z⁻¹) * w) := by group
      _ = (z * w * z⁻¹) * w := by rw [hc1, one_mul]
  -- the two elements generate an injective copy of ℤ²
  refine ⟨w, hKG hwW.1, z * w * z⁻¹, hKG hw'K, hcomm, ?_⟩
  have hx₀C : x₀ ∈ connectedComponentIn (supp f ∪ supp g) x₀ := mem_connectedComponentIn hx₀U
  have hx₀nw' : x₀ ∉ supp (z * w * z⁻¹) := by
    rcases hdisj x₀ hx₀C with h | h
    · exact absurd hx₀ h
    · exact h
  -- the conjugate moves `z x₀`, which `w` leaves alone
  have hzx₀ : z x₀ ∈ supp (z * w * z⁻¹) := by
    rw [BrinSquier.supp_conj z w]; exact ⟨x₀, hx₀, rfl⟩
  have hzx₀C : z x₀ ∈ connectedComponentIn (supp f ∪ supp g) x₀ := pres_comp hzfix hx₀C
  have hzx₀nw : z x₀ ∉ supp w := by
    rcases hdisj (z x₀) hzx₀C with h | h
    · exact h
    · exact absurd hzx₀ h
  intro p q hpq
  dsimp only at hpq
  have hfixw' : (z * w * z⁻¹) x₀ = x₀ := not_not.1 hx₀nw'
  have h1 : (w ^ p.1) x₀ = (w ^ q.1) x₀ := by
    have h0 : (w ^ p.1) (((z * w * z⁻¹) ^ p.2) x₀)
        = (w ^ q.1) (((z * w * z⁻¹) ^ q.2) x₀) :=
      congrArg (fun (h : ℝ ≃o ℝ) => h x₀) hpq
    rwa [zpow_fix hfixw' p.2, zpow_fix hfixw' q.2] at h0
  have hp1 : p.1 = q.1 := by
    by_contra hcon
    have h2 : (w ^ (p.1 - q.1)) ((w ^ q.1) x₀) = (w ^ q.1) x₀ := by
      show (w ^ (p.1 - q.1) * w ^ q.1) x₀ = _
      rw [← zpow_add, show p.1 - q.1 + q.1 = p.1 by ring]
      exact h1
    exact HomeoLine.zpow_moves_of_moves (mem_supp_zpow hx₀ q.1) (p.1 - q.1)
      (sub_ne_zero.2 hcon) h2
  have h3 : ((z * w * z⁻¹) ^ p.2) (z x₀) = ((z * w * z⁻¹) ^ q.2) (z x₀) := by
    have h0 : (w ^ p.1) (((z * w * z⁻¹) ^ p.2) (z x₀))
        = (w ^ q.1) (((z * w * z⁻¹) ^ q.2) (z x₀)) :=
      congrArg (fun (h : ℝ ≃o ℝ) => h (z x₀)) hpq
    have e1 : w (((z * w * z⁻¹) ^ p.2) (z x₀)) = ((z * w * z⁻¹) ^ p.2) (z x₀) := by
      rcases hdisj _ (pres_comp (zpow_fixes_compl hw'fix p.2) hzx₀C) with h | h
      · exact not_not.1 h
      · exact absurd (mem_supp_zpow hzx₀ p.2) h
    have e2 : w (((z * w * z⁻¹) ^ q.2) (z x₀)) = ((z * w * z⁻¹) ^ q.2) (z x₀) := by
      rcases hdisj _ (pres_comp (zpow_fixes_compl hw'fix q.2) hzx₀C) with h | h
      · exact not_not.1 h
      · exact absurd (mem_supp_zpow hzx₀ q.2) h
    rwa [zpow_fix e1 p.1, zpow_fix e2 q.1] at h0
  have hp2 : p.2 = q.2 := by
    by_contra hcon
    have h4 : ((z * w * z⁻¹) ^ (p.2 - q.2)) (((z * w * z⁻¹) ^ q.2) (z x₀))
        = ((z * w * z⁻¹) ^ q.2) (z x₀) := by
      show ((z * w * z⁻¹) ^ (p.2 - q.2) * (z * w * z⁻¹) ^ q.2) (z x₀) = _
      rw [← zpow_add, show p.2 - q.2 + q.2 = p.2 by ring]
      exact h3
    exact HomeoLine.zpow_moves_of_moves (mem_supp_zpow hzx₀ q.2) (p.2 - q.2)
      (sub_ne_zero.2 hcon) h4
  exact Prod.ext hp1 hp2
