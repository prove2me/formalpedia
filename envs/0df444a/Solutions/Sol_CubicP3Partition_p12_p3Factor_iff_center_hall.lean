-- Prove2me | solution 1 for CubicP3Partition.p12_p3Factor_iff_center_hall
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T19:28:19.565526+00:00
-- url     : https://prove2.me/submissions/fd70e6be-9639-43fc-8669-3c150f9753c9

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_5719a22c9e_R03CenterHall

/-!
# R03 center--Hall equivalence

For a finite graph, a P3 factor is equivalent to a finite center set of one
third of the vertices whose external neighborhood satisfies the two-fold Hall
inequality.  The proof uses a duplicated-center Hall matching; no cubicity or
connectivity assumption is needed for this equivalence.
-/

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

lemma p12PositionEquiv_symm_inr_zero (k : Nat) (i : Fin k) :
    (p12PositionEquiv k).symm (Sum.inr (i, (0 : Fin 2))) = (i, (0 : Fin 3)) := by
  apply (p12PositionEquiv k).injective
  rw [(p12PositionEquiv k).apply_symm_apply]
  simp [p12PositionEquiv]

lemma p12PositionEquiv_symm_inr_one (k : Nat) (i : Fin k) :
    (p12PositionEquiv k).symm (Sum.inr (i, (1 : Fin 2))) = (i, (2 : Fin 3)) := by
  apply (p12PositionEquiv k).injective
  rw [(p12PositionEquiv k).apply_symm_apply]
  simp [p12PositionEquiv]

theorem p12_duplicate_hall [Fintype V] {G : SimpleGraph V} {C : Finset V}
    (hHall : p12CenterHall G C) :
    ∀ A : Finset (↥C × Fin 2),
      A.card ≤ (p12DuplicateNeighbors G C A).card := by
  classical
  intro A
  let Psub : Finset C := A.image Prod.fst
  let P : Finset V := Psub.image Subtype.val
  have hPsub_card : Psub.card = P.card := by
    symm
    exact Finset.card_image_of_injective Psub Subtype.val_injective
  have hPsub_subset : Psub ⊆ (Finset.univ : Finset C) := by
    intro x hx
    simp
  have hP_subset : P ⊆ C := by
    intro x hx
    simp only [P, Finset.mem_image] at hx
    rcases hx with ⟨x', hx', rfl⟩
    exact x'.property
  have hA_subset : A ⊆ Psub ×ˢ (Finset.univ : Finset (Fin 2)) := by
    intro z hz
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hA_card : A.card ≤ 2 * P.card := by
    calc
      A.card ≤ (Psub ×ˢ (Finset.univ : Finset (Fin 2))).card :=
        Finset.card_le_card hA_subset
      _ = Psub.card * 2 := by simp
      _ = 2 * P.card := by rw [hPsub_card]; omega
  have hHallP : 2 * P.card ≤ (p12ExternalNeighborFinset G C P).card :=
    hHall P hP_subset
  have hN_eq :
      p12DuplicateNeighbors G C A = p12ExternalNeighborFinset G C P := by
    ext w
    simp [p12DuplicateNeighbors, p12ExternalNeighborFinset, P, Psub]
  calc
    A.card ≤ 2 * P.card := hA_card
    _ ≤ (p12ExternalNeighborFinset G C P).card := hHallP
    _ = (p12DuplicateNeighbors G C A).card := by rw [hN_eq]

theorem p12_exists_duplicate_injection [Fintype V] {G : SimpleGraph V}
    {C : Finset V} (hHall : p12CenterHall G C) :
    ∃ f : (↥C × Fin 2) → V,
      Function.Injective f ∧ ∀ z, G.Adj z.1.1 (f z) ∧ f z ∉ C := by
  classical
  let R : (↥C × Fin 2) → V → Prop :=
    fun z w => G.Adj z.1.1 w ∧ w ∉ C
  have hDup : ∀ A : Finset (↥C × Fin 2),
      A.card ≤ ({w : V | ∃ z ∈ A, R z w} : Finset V).card := by
    intro A
    change A.card ≤ (p12DuplicateNeighbors G C A).card
    exact p12_duplicate_hall hHall A
  obtain ⟨f, hf, hrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hDup
  exact ⟨f, hf, fun z => hrel z⟩

/-- Hall plus the one-third size equation gives a bijection to the outside vertices. -/
theorem p12_hall_outside_equiv [Fintype V] {G : SimpleGraph V}
    {C : Finset V} (hSize : p12CenterSize C)
    (hHall : p12CenterHall G C) :
    ∃ e : (↥C × Fin 2) ≃ {w : V // w ∉ C},
      ∀ z, G.Adj z.1.1 (e z).1 := by
  classical
  let _ : Fintype {w : V // w ∉ C} := Fintype.ofFinite _
  obtain ⟨f, hf, hrel⟩ := p12_exists_duplicate_injection hHall
  let fo : (↥C × Fin 2) → {w : V // w ∉ C} :=
    fun z => ⟨f z, (hrel z).2⟩
  have hfo : Function.Injective fo := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  have hcard : Fintype.card (↥C × Fin 2) =
      Fintype.card {w : V // w ∉ C} := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_compl]
    rw [Fintype.card_coe C]
    dsimp [p12CenterSize] at hSize
    omega
  have hbij : Function.Bijective fo :=
    (Fintype.bijective_iff_injective_and_card fo).mpr ⟨hfo, hcard⟩
  refine ⟨Equiv.ofBijective fo hbij, ?_⟩
  intro z
  exact (hrel z).1

/-- Construct a P3 factor from a center set and its duplicated-center Hall matching. -/
theorem p12_center_hall_to_p3Factor [Fintype V] {G : SimpleGraph V}
    {C : Finset V} (hSize : p12CenterSize C)
    (hHall : p12CenterHall G C) : Nonempty (P3Factor G) := by
  classical
  let _ : Fintype {w : V // w ∉ C} := Fintype.ofFinite _
  obtain ⟨outsideEquiv, hAdj⟩ := p12_hall_outside_equiv hSize hHall
  let centerEquiv : Fin C.card ≃ (↥C) :=
    (finCongr (Fintype.card_coe C).symm).trans (Fintype.equivFin C).symm
  let leafEquiv : (Fin C.card × Fin 2) ≃ (↥C × Fin 2) :=
    Equiv.prodCongr centerEquiv (Equiv.refl (Fin 2))
  let place : (Fin C.card × Fin 3) ≃ V :=
    (p12PositionEquiv C.card).trans <|
      (Equiv.sumCongr centerEquiv (leafEquiv.trans outsideEquiv)).trans
        (Equiv.sumCompl (fun w : V => w ∈ C))
  refine ⟨{ blockCount := C.card, place := place, edge01 := ?_, edge12 := ?_ }⟩
  · intro i
    have h := hAdj (centerEquiv i, 0)
    simpa [place, p12PositionEquiv, centerEquiv, leafEquiv] using h.symm
  · intro i
    have h := hAdj (centerEquiv i, 1)
    simpa [place, p12PositionEquiv, centerEquiv, leafEquiv] using h

/-- A P3 factor supplies a center set satisfying the two-fold Hall inequalities. -/
theorem p12_p3Factor_to_center_hall [Fintype V] {G : SimpleGraph V} :
    Nonempty (P3Factor G) →
      ∃ C : Finset V, p12CenterSize C ∧ p12CenterHall G C := by
  classical
  rintro ⟨p⟩
  let center : Fin p.blockCount → V := fun i => p.place (i, 1)
  have hcenter_inj : Function.Injective center := by
    intro i j hij
    have hpos : (i, (1 : Fin 3)) = (j, 1) := by
      apply p.place.injective
      simpa [center] using hij
    exact congrArg Prod.fst hpos
  let C : Finset V := Finset.univ.image center
  have hC : C = Finset.univ.image center := rfl
  have hCcard : C.card = p.blockCount := by
    dsimp [C]
    rw [Finset.card_image_of_injective _ hcenter_inj]
    simp
  have hSize : p12CenterSize C := by
    dsimp [p12CenterSize]
    rw [hCcard]
    have hplaceCard : Fintype.card (Fin p.blockCount × Fin 3) = Fintype.card V :=
      Fintype.card_congr p.place
    simpa [Fintype.card_prod, Nat.mul_comm] using hplaceCard
  let leafMap : (Fin p.blockCount × Fin 2) → V := fun z =>
    p.place ((p12PositionEquiv p.blockCount).symm (Sum.inr z))
  have hleaf_inj : Function.Injective leafMap := by
    intro x y hxy
    have hpos :
        (p12PositionEquiv p.blockCount).symm (Sum.inr x) =
          (p12PositionEquiv p.blockCount).symm (Sum.inr y) := by
      apply p.place.injective
      simpa [leafMap] using hxy
    have hsum : (Sum.inr x : Fin p.blockCount ⊕ (Fin p.blockCount × Fin 2)) =
        Sum.inr y := by
      simpa using congrArg (p12PositionEquiv p.blockCount) hpos
    exact Sum.inr.inj hsum
  have hcenter_ne_leaf : ∀ i z, center i ≠ leafMap z := by
    intro i z heq
    have hpos :
        (i, (1 : Fin 3)) =
          (p12PositionEquiv p.blockCount).symm (Sum.inr z) := by
      apply p.place.injective
      simpa [center, leafMap] using heq
    have hsum :
        (Sum.inl i : Fin p.blockCount ⊕ (Fin p.blockCount × Fin 2)) =
          Sum.inr z := by
      calc
        Sum.inl i = p12PositionEquiv p.blockCount (i, 1) := by
          simp [p12PositionEquiv]
        _ = p12PositionEquiv p.blockCount
            ((p12PositionEquiv p.blockCount).symm (Sum.inr z)) :=
          congrArg (p12PositionEquiv p.blockCount) hpos
        _ = Sum.inr z := (p12PositionEquiv p.blockCount).apply_symm_apply _
    exact Sum.inl_ne_inr hsum
  have hleaf_outside : ∀ z, leafMap z ∉ C := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _hi, hEq⟩
    exact hcenter_ne_leaf i z hEq
  have hleaf_adj : ∀ i j, G.Adj (center i) (leafMap (i, j)) := by
    intro i j
    fin_cases j
    · have h := p.edge01 i
      dsimp [leafMap]
      rw [p12PositionEquiv_symm_inr_zero]
      simpa [center] using h.symm
    · have h := p.edge12 i
      dsimp [leafMap]
      rw [p12PositionEquiv_symm_inr_one]
      simpa [center] using h
  have hHall : p12CenterHall G C := by
    intro A hA
    let I : Finset (Fin p.blockCount) := A.preimage center hcenter_inj.injOn
    have hIimage : I.image center = A := by
      have hpre : I.image center = {x ∈ A | x ∈ Set.range center} := by
        exact Finset.image_preimage center A hcenter_inj.injOn
      rw [hpre]
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        rcases Finset.mem_image.mp (hC ▸ hA hx) with ⟨i, _hi, hxi⟩
        exact ⟨i, hxi⟩
    have hIcard : I.card = A.card := by
      calc
        I.card = (I.image center).card :=
          (Finset.card_image_of_injective I hcenter_inj).symm
        _ = A.card := by rw [hIimage]
    let Lindex : Finset (Fin p.blockCount × Fin 2) :=
      I ×ˢ (Finset.univ : Finset (Fin 2))
    let L : Finset V := Lindex.image leafMap
    have hLsubset : L ⊆ p12ExternalNeighborFinset G C A := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      change z ∈ I ×ˢ (Finset.univ : Finset (Fin 2)) at hz
      have hi : z.1 ∈ I := by
        simpa only [Finset.mem_product, Finset.mem_univ, and_true] using hz
      have hcenterA : center z.1 ∈ A := Finset.mem_preimage.mp hi
      apply Finset.mem_biUnion.mpr
      refine ⟨center z.1, hcenterA, ?_⟩
      refine Finset.mem_sdiff.mpr ⟨?_, hleaf_outside z⟩
      exact (G.mem_neighborFinset _ _).mpr (hleaf_adj z.1 z.2)
    have hLcard : L.card = 2 * A.card := by
      dsimp [L]
      rw [Finset.card_image_of_injective _ hleaf_inj]
      simp [Lindex, hIcard, Nat.mul_comm]
    calc
      2 * A.card = L.card := hLcard.symm
      _ ≤ (p12ExternalNeighborFinset G C A).card := Finset.card_le_card hLsubset
  exact ⟨C, hSize, hHall⟩


end
end CubicP3Partition

open CubicP3Partition
universe u
variable {V : Type u}
theorem solution [Fintype V] {G : SimpleGraph V} :
    Nonempty (P3Factor G) ↔
      ∃ C : Finset V, p12CenterSize C ∧ p12CenterHall G C := by
  constructor
  · exact p12_p3Factor_to_center_hall
  · rintro ⟨C, hSize, hHall⟩
    exact p12_center_hall_to_p3Factor hSize hHall
