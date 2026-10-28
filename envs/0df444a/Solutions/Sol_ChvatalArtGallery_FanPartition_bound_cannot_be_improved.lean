-- Prove2me | solution 1 for ChvatalArtGallery.FanPartition.bound_cannot_be_improved
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:44:36.171784+00:00
-- url     : https://prove2.me/submissions/9cef1cc2-4732-46b8-a2f3-18750ce5aa81

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

private lemma cdist_eq {n : ℕ} (a b : Fin n) :
    cdist a b = if a.val ≤ b.val then b.val - a.val else b.val + n - a.val := by
  unfold cdist
  have ha := a.isLt
  have hb := b.isLt
  split_ifs with h
  · have h1 : b.val + n - a.val = (b.val - a.val) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma crosses_irrefl {n : ℕ} (e : Sym2 (Fin n)) : ¬ Crosses e e := by
  rintro ⟨a, b, c, d, hab, hcd, h1, h2, h3⟩
  have heq : s(a, b) = s(c, d) := hab.symm.trans hcd
  rw [Sym2.eq_iff] at heq
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  simp only [cdist_eq] at h1 h2 h3
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs at h1 h2 h3 <;> omega

private lemma crosses_symm {n : ℕ} {e f : Sym2 (Fin n)} (h : Crosses e f) : Crosses f e := by
  rcases h with ⟨a, b, c, d, rfl, rfl, h1, h2, h3⟩
  refine ⟨c, d, b, a, rfl, Sym2.eq_swap, ?_⟩
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  simp only [cdist_eq] at h1 h2 h3 ⊢
  split_ifs at h1 h2 h3 ⊢ <;> omega

private def earV0 (n : ℕ) (i : Fin (n / 3)) : Fin n := ⟨3 * i.val, by omega⟩
private def earV1 (n : ℕ) (i : Fin (n / 3)) : Fin n := ⟨3 * i.val + 1, by omega⟩
private def earV2 (n : ℕ) (i : Fin (n / 3)) : Fin n := ⟨3 * i.val + 2, by omega⟩

private def earChord (n : ℕ) (i : Fin (n / 3)) : Sym2 (Fin n) := s(earV0 n i, earV2 n i)

private def earTri (n : ℕ) (i : Fin (n / 3)) : Finset (Fin n) :=
  {earV0 n i, earV1 n i, earV2 n i}

private lemma cdist_earV0_earV2 (n : ℕ) (i : Fin (n / 3)) :
    cdist (earV0 n i) (earV2 n i) = 2 := by
  have hi := i.isLt
  simp only [cdist_eq, earV0, earV2]
  split_ifs <;> omega

private lemma cdist_earV2_earV0 (n : ℕ) (i : Fin (n / 3)) :
    cdist (earV2 n i) (earV0 n i) = n - 2 := by
  have hi := i.isLt
  simp only [cdist_eq, earV0, earV2]
  split_ifs <;> omega

private lemma eq_earV1_of_cdist_earV0 {n : ℕ} (i : Fin (n / 3)) (x : Fin n)
    (h1 : 0 < cdist (earV0 n i) x) (h2 : cdist (earV0 n i) x < 2) :
    x.val = 3 * i.val + 1 := by
  have hi := i.isLt; have hx := x.isLt
  simp only [cdist_eq, earV0] at h1 h2
  split_ifs at h1 h2 <;> omega

private lemma eq_earV1_of_cdist_earV2 {n : ℕ} (i : Fin (n / 3)) (x : Fin n)
    (h : n - 2 < cdist (earV2 n i) x) :
    x.val = 3 * i.val + 1 := by
  have hi := i.isLt; have hx := x.isLt
  simp only [cdist_eq, earV2] at h
  split_ifs at h <;> omega

private lemma earChord_not_crosses (n : ℕ) (i j : Fin (n / 3)) :
    ¬ Crosses (earChord n i) (earChord n j) := by
  rintro ⟨a, b, c, d, hab, hcd, h1, h2, h3⟩
  unfold earChord at hab hcd
  rw [Sym2.eq_iff] at hab hcd
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [cdist_earV0_earV2] at h2
    have hc := eq_earV1_of_cdist_earV0 i c h1 h2
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [earV0, earV2] at hc <;> omega
  · rw [cdist_earV2_earV0] at h3
    have hd := eq_earV1_of_cdist_earV2 i d h3
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [earV0, earV2] at hd <;> omega

private lemma earEdge01 (n : ℕ) (i : Fin (n / 3)) :
    IsBoundaryEdge s(earV0 n i, earV1 n i) := by
  refine ⟨earV0 n i, earV1 n i, rfl, ?_⟩
  have hi := i.isLt
  simp only [cdist_eq, earV0, earV1]
  split_ifs <;> omega

private lemma earEdge12 (n : ℕ) (i : Fin (n / 3)) :
    IsBoundaryEdge s(earV1 n i, earV2 n i) := by
  refine ⟨earV1 n i, earV2 n i, rfl, ?_⟩
  have hi := i.isLt
  simp only [cdist_eq, earV1, earV2]
  split_ifs <;> omega

private lemma earEdge02_boundary_of_eq3 (n : ℕ) (hn : n = 3) (i : Fin (n / 3)) :
    IsBoundaryEdge s(earV0 n i, earV2 n i) := by
  refine ⟨earV2 n i, earV0 n i, Sym2.eq_swap, ?_⟩
  have hi := i.isLt
  simp only [cdist_eq, earV0, earV2]
  split_ifs <;> omega

private lemma earChord_isDiagonal_of_ge4 (n : ℕ) (hn : 4 ≤ n) (i : Fin (n / 3)) :
    IsDiagonal (earChord n i) := by
  intro a b hab
  unfold earChord at hab
  rw [Sym2.eq_iff] at hab
  have hi := i.isLt
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by simp [earV0, earV2, Fin.ext_iff], ?_, ?_⟩ <;>
      { simp only [cdist_eq, earV0, earV2]; split_ifs <;> omega }
  · refine ⟨by simp [earV0, earV2, Fin.ext_iff], ?_, ?_⟩ <;>
      { simp only [cdist_eq, earV0, earV2]; split_ifs <;> omega }

private lemma exists_triangulation_extending (n : ℕ) (hn : 3 ≤ n)
    (D₀ : Finset (Sym2 (Fin n)))
    (hD₀_diag : ∀ e ∈ D₀, IsDiagonal e)
    (hD₀_nc : ∀ e ∈ D₀, ∀ f ∈ D₀, ¬ Crosses e f) :
    ∃ D : Finset (Sym2 (Fin n)), D₀ ⊆ D ∧ IsTriangulation n D := by
  by_cases hmax : ∀ e : Sym2 (Fin n), IsDiagonal e → (∀ f ∈ D₀, ¬ Crosses e f) → e ∈ D₀
  · exact ⟨D₀, Finset.Subset.rfl, hn, hD₀_diag, hD₀_nc, hmax⟩
  · push Not at hmax
    rcases hmax with ⟨e, he_diag, he_nc, he_not_mem⟩
    have hcard_lt :
        (Finset.univ : Finset (Sym2 (Fin n))).card - (insert e D₀).card <
          (Finset.univ : Finset (Sym2 (Fin n))).card - D₀.card := by
      have hle : (insert e D₀).card ≤ (Finset.univ : Finset (Sym2 (Fin n))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_insert_of_notMem he_not_mem] at hle ⊢
      omega
    have hins_diag : ∀ x ∈ insert e D₀, IsDiagonal x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxD
      · exact he_diag
      · exact hD₀_diag x hxD
    have hins_nc : ∀ x ∈ insert e D₀, ∀ y ∈ insert e D₀, ¬ Crosses x y := by
      intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hxD <;>
        rcases Finset.mem_insert.mp hy with rfl | hyD
      · exact crosses_irrefl _
      · exact he_nc y hyD
      · exact fun h => he_nc x hxD (crosses_symm h)
      · exact hD₀_nc x hxD y hyD
    obtain ⟨D, hsub, htri⟩ :=
      exists_triangulation_extending n hn (insert e D₀) hins_diag hins_nc
    exact ⟨D, (Finset.subset_insert e D₀).trans hsub, htri⟩
termination_by (Finset.univ : Finset (Sym2 (Fin n))).card - D₀.card

private lemma earTri_mem_triangles (n : ℕ) (hn : 3 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : ∀ i : Fin (n / 3), IsDiagonal (earChord n i) → earChord n i ∈ D)
    (i : Fin (n / 3)) : earTri n i ∈ triangles n D := by
  have h01 : earV0 n i ≠ earV1 n i := by simp [earV0, earV1, Fin.ext_iff]
  have h12 : earV1 n i ≠ earV2 n i := by simp [earV1, earV2, Fin.ext_iff]
  have h02 : earV0 n i ≠ earV2 n i := by simp [earV0, earV2, Fin.ext_iff]
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨?_, ?_⟩
  · unfold earTri
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h12]
    · simp [h01, h02]
  · intro a ha b hb hab
    unfold earTri at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hedge01 : IsEdge D s(earV0 n i, earV1 n i) := Or.inl (earEdge01 n i)
    have hedge12 : IsEdge D s(earV1 n i, earV2 n i) := Or.inl (earEdge12 n i)
    have hedge02 : IsEdge D s(earV0 n i, earV2 n i) := by
      by_cases hn4 : 4 ≤ n
      · exact Or.inr (hD i (earChord_isDiagonal_of_ge4 n hn4 i))
      · exact Or.inl (earEdge02_boundary_of_eq3 n (by omega) i)
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hedge01
    · exact hedge02
    · rw [Sym2.eq_swap]; exact hedge01
    · exact (hab rfl).elim
    · exact hedge12
    · rw [Sym2.eq_swap]; exact hedge02
    · rw [Sym2.eq_swap]; exact hedge12
    · exact (hab rfl).elim

private lemma earTri_eq_of_mem (n : ℕ) {i j : Fin (n / 3)} {c : Fin n}
    (hi : c ∈ earTri n i) (hj : c ∈ earTri n j) : i = j := by
  unfold earTri at hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  ext
  rcases hi with rfl | rfl | rfl <;> rcases hj with h | h | h <;>
    simp only [Fin.ext_iff, earV0, earV1, earV2] at h <;> omega

private lemma isFan_exists_common_vertex (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (F : Finset (Finset (Fin n))) (hF : IsFan n D F) :
    ∃ c : Fin n, ∀ T ∈ F, c ∈ T := by
  rcases hF with ⟨hF_sub, ⟨T₀, hT₀⟩, hF_conn, c, hc⟩
  by_cases h1 : ∀ T ∈ F, T = T₀
  · have hT₀_tri := hF_sub hT₀
    simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard] at hT₀_tri
    obtain ⟨c₀, hc₀⟩ : T₀.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨c₀, fun T hT => h1 T hT ▸ hc₀⟩
  · refine ⟨c, fun T hT => ?_⟩
    have hex : ∃ Y ∈ F, Adjacent T Y := by
      by_contra hno
      push Not at hno
      have hS_eq : ({T} : Finset (Finset (Fin n))) = F := by
        apply hF_conn {T} (Finset.singleton_subset_iff.mpr hT) (Finset.singleton_nonempty T)
        intro X hX Y hY hadj
        rw [Finset.mem_singleton] at hX
        subst hX
        exact (hno Y hY hadj).elim
      apply h1
      intro T' hT'
      have hT'_eq : T' = T := Finset.mem_singleton.mp (hS_eq.symm ▸ hT')
      have hT₀_eq : T₀ = T := Finset.mem_singleton.mp (hS_eq.symm ▸ hT₀)
      exact hT'_eq.trans hT₀_eq.symm
    rcases hex with ⟨Y, hY, hadj⟩
    exact (Finset.mem_inter.mp (hc T hT Y hY hadj)).1

/-- p. 41: the bound ⌊n/3⌋ cannot be improved — for every n ≥ 3 some n-triangulation admits no
partition into fewer than ⌊n/3⌋ fans. -/
theorem bound_cannot_be_improved (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : Finset (Sym2 (Fin n)), IsTriangulation n D ∧
      ∀ P : Finset (Finset (Finset (Fin n))), IsFanPartition n D P → n / 3 ≤ P.card := by
  let D₀ : Finset (Sym2 (Fin n)) :=
    ((Finset.univ : Finset (Fin (n / 3))).image (earChord n)).filter IsDiagonal
  have hD₀_diag : ∀ e ∈ D₀, IsDiagonal e := fun _ he => (Finset.mem_filter.mp he).2
  have hD₀_nc : ∀ e ∈ D₀, ∀ f ∈ D₀, ¬ Crosses e f := by
    intro e he f hf
    rcases Finset.mem_image.mp (Finset.mem_filter.mp he).1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hf).1 with ⟨j, _, rfl⟩
    exact earChord_not_crosses n i j
  obtain ⟨D, hD₀_sub, hD_tri⟩ := exists_triangulation_extending n hn D₀ hD₀_diag hD₀_nc
  refine ⟨D, hD_tri, ?_⟩
  intro P ⟨hP_fan, _, hP_union⟩
  have hmem_D : ∀ i : Fin (n / 3), IsDiagonal (earChord n i) → earChord n i ∈ D := by
    intro i hi
    apply hD₀_sub
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩
  have hmem_P : ∀ i : Fin (n / 3), ∃ F ∈ P, earTri n i ∈ F := by
    intro i
    have htri : earTri n i ∈ P.biUnion id := hP_union.symm ▸ earTri_mem_triangles n hn D hmem_D i
    simpa only [Finset.mem_biUnion, id_eq] using htri
  choose f hfP hf_mem using hmem_P
  have hf_inj : Function.Injective f := by
    intro i j hij
    obtain ⟨c, hc⟩ := isFan_exists_common_vertex n D (f i) (hP_fan (f i) (hfP i))
    have hci : c ∈ earTri n i := hc (earTri n i) (hf_mem i)
    have hcj : c ∈ earTri n j := hc (earTri n j) (hij ▸ hf_mem j)
    exact earTri_eq_of_mem n hci hcj
  calc
    n / 3 = (Finset.univ : Finset (Fin (n / 3))).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
    _ ≤ P.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun i _ => hfP i)

end ChvatalArtGallery.FanPartition

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : Finset (Sym2 (Fin n)), ChvatalArtGallery.FanPartition.IsTriangulation n D ∧
      ∀ P : Finset (Finset (Finset (Fin n))),
        ChvatalArtGallery.FanPartition.IsFanPartition n D P → n / 3 ≤ P.card :=
  ChvatalArtGallery.FanPartition.bound_cannot_be_improved n hn
