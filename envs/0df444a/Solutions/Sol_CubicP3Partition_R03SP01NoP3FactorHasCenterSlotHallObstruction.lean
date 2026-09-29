-- Prove2me | solution 1 for CubicP3Partition.R03SP01NoP3FactorHasCenterSlotHallObstruction
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:43.440455+00:00
-- url     : https://prove2.me/submissions/b9051922-7225-4b0a-9520-0939f6f62b3c

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1

universe w
namespace CubicP3Partition
noncomputable def R03SP01FactorCenterSet
    {V : Type w} [Fintype V]
    {G : SimpleGraph V} (p : P3Factor G) : Finset V := by
  classical
  exact Finset.univ.image (fun i : Fin p.blockCount =>
    p.place (i, (1 : Fin 3)))
end CubicP3Partition


namespace CubicP3Partition

universe u

set_option maxRecDepth 100000

theorem R03SP01CenterSlotCertificateP3Factor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : R03SP01CenterSlotCertificate G C) :
    Nonempty (P3Factor G) := by
  classical
  rcases hC with ⟨n, eC, eL, hAdj⟩
  let jTo : Fin 3 → Fin 2 ⊕ Fin 1 := fun j =>
    if j = 0 then Sum.inl 0 else if j = 1 then Sum.inr 0 else Sum.inl 1
  let jInv : Fin 2 ⊕ Fin 1 → Fin 3 := fun s =>
    match s with
    | Sum.inl j => if j = 0 then 0 else 2
    | Sum.inr _ => 1
  have hjLeft : Function.LeftInverse jInv jTo := by
    intro j
    fin_cases j <;> simp [jTo, jInv]
  have hjRight : Function.RightInverse jInv jTo := by
    intro s
    cases s with
    | inl j =>
        fin_cases j <;> simp [jTo, jInv]
    | inr j =>
        fin_cases j <;> simp [jTo, jInv]
  let jEquiv : Fin 3 ≃ Fin 2 ⊕ Fin 1 :=
    { toFun := jTo
      invFun := jInv
      left_inv := hjLeft
      right_inv := hjRight }
  let Cset : Set V := (↑C : Set V)
  let place : (Fin n × Fin 3) ≃ V :=
    (Equiv.prodCongr (Equiv.refl (Fin n)) jEquiv).trans
      ((Equiv.prodSumDistrib (Fin n) (Fin 2) (Fin 1)).trans
        ((Equiv.sumCongr eL
          ((Equiv.prodUnique (Fin n) (Fin 1)).trans eC)).trans
          ((Equiv.sumComm (Csetᶜ : Set V) Cset).trans
            (Equiv.Set.sumCompl Cset))))
  have h0 (i : Fin n) : place (i, (0 : Fin 3)) = (eL (i, 0) : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  have h1 (i : Fin n) : place (i, (1 : Fin 3)) = (eC i : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  have h2 (i : Fin n) : place (i, (2 : Fin 3)) = (eL (i, 1) : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  refine ⟨{
    blockCount := n
    place := place
    edge01 := ?_
    edge12 := ?_ }⟩
  · intro i
    rw [h0, h1]
    exact hAdj i 0
  · intro i
    rw [h1, h2]
    exact SimpleGraph.Adj.symm (hAdj i 1)

#print axioms R03SP01CenterSlotCertificate
#print axioms R03SP01CenterSlotCertificateP3Factor

theorem R03SP01CenterSlotCertificateAtIffHall
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2) :
    R03SP01CenterSlotCertificateAt G C n eC ↔
      R03SP01CenterSlotHallCondition G C n eC := by
  classical
  let rel : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2) → Prop :=
    fun a b => G.Adj (a : V) (eC b.1 : V)
  constructor
  · rintro ⟨eL, hAdj⟩
    intro A
    let S : Finset (Fin n × Fin 2) := A.image eL.symm
    have hSsub : S ⊆ Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b) := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨a, ha, ?_⟩
      simpa [rel] using hAdj ((eL.symm a).1) ((eL.symm a).2)
    have hScard : S.card = A.card := by
      dsimp [S]
      exact Finset.card_image_of_injective A eL.symm.injective
    change A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
      ∃ a ∈ A, rel a b)).card
    rw [← hScard]
    exact Finset.card_le_card hSsub
  · intro hHall
    change ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b)).card at hHall
    obtain ⟨f, hinj, hf⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall
    have hcard' : Fintype.card ((↑C : Set V)ᶜ : Set V) =
        Fintype.card (Fin n × Fin 2) := by
      simpa using hcard
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩
    let ef : ((↑C : Set V)ᶜ : Set V) ≃ (Fin n × Fin 2) :=
      Equiv.ofBijective f hfbij
    let eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V) := ef.symm
    refine ⟨eL, ?_⟩
    intro i j
    have hrel := hf (eL (i, j))
    have heq : f (eL (i, j)) = (i, j) := ef.apply_symm_apply (i, j)
    rw [heq] at hrel
    exact hrel

#print axioms R03SP01CenterSlotCertificateAt
#print axioms R03SP01CenterSlotHallCondition
#print axioms R03SP01CenterSlotCertificateAtIffHall

/-- Convert an injective capacity-two assignment of all complementary
vertices into a center-slot certificate.  The cardinality equality upgrades
the finite injection to a bijection, so no unmatched leaf is hidden. -/
theorem R03SP01CenterSlotCertificateOfInjectiveAssignment
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (f : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2)
    (hinj : Function.Injective f)
    (hAdj : ∀ x : ((↑C : Set V)ᶜ : Set V),
      G.Adj (x : V) (eC (f x).1 : V)) :
    R03SP01CenterSlotCertificate G C := by
  classical
  have hcard' : Fintype.card ((↑C : Set V)ᶜ : Set V) = Fintype.card (Fin n × Fin 2) := by
    simpa using hcard
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩
  let ef : ((↑C : Set V)ᶜ : Set V) ≃ (Fin n × Fin 2) := Equiv.ofBijective f hbij
  let eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V) := ef.symm
  refine ⟨n, eC, eL, ?_⟩
  intro i j
  have h := hAdj (eL (i, j))
  have hf : f (eL (i, j)) = (i, j) := ef.apply_symm_apply (i, j)
  rw [hf] at h
  exact h

#print axioms R03SP01CenterSlotCertificateOfInjectiveAssignment

/-- Hall's finite condition is a sufficient certificate for the integral
center-slot assignment.  The right-hand side counts distinct capacity slots,
not just distinct center vertices. -/
theorem R03SP01CenterSlotHallP3Factor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2)
    (hHall : ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, G.Adj (a : V) (eC b.1 : V))).card) :
    Nonempty (P3Factor G) := by
  classical
  let rel : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2) → Prop :=
    fun a b => G.Adj (a : V) (eC b.1 : V)
  have hHall' : ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b)).card := by
    intro A
    simpa [rel] using hHall A
  obtain ⟨f, hinj, hf⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall'
  apply R03SP01CenterSlotCertificateP3Factor G C
  apply R03SP01CenterSlotCertificateOfInjectiveAssignment G C n eC f hcard hinj
  intro x
  exact hf x

#print axioms R03SP01CenterSlotHallP3Factor

/-- Cardinality-specialized form for a proposed root center set.  Here the
center enumeration is the canonical finite enumeration of the set, and the
order identity supplies exactly two leaf slots per center. -/
theorem R03SP01CenterSlotHallP3FactorOfCard
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype (↑C : Set V)]
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (eC : Fin C.card ≃ (↑C : Set V))
    (hcardV : Fintype.card V = 3 * C.card)
    (hHall : ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin C.card × Fin 2 =>
        ∃ a ∈ A, G.Adj (a : V) (eC b.1 : V))).card) :
    Nonempty (P3Factor G) := by
  classical
  let Cset : Set V := (↑C : Set V)
  have hsum : Fintype.card Cset +
      Fintype.card ((Csetᶜ : Set V)) = Fintype.card V := by
    simpa [Cset] using
      (Fintype.card_congr (Equiv.Set.sumCompl Cset))
  have hCcard : Fintype.card Cset = C.card := by
    simpa [Cset]
  have hcomp : Fintype.card ((Csetᶜ : Set V)) = C.card * 2 := by
    omega
  apply R03SP01CenterSlotHallP3Factor G C C.card eC hcomp
  intro A
  simpa [Cset] using hHall A

#print axioms R03SP01CenterSlotHallP3FactorOfCard

theorem R03SP01P3FactorCenterSlotCertificate
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} (p : P3Factor G) :
    R03SP01CenterSlotCertificate G (R03SP01FactorCenterSet p) := by
  classical
  let C : Finset V := R03SP01FactorCenterSet p
  let centerMap : Fin p.blockCount → V :=
    fun i => p.place (i, (1 : Fin 3))
  have hcenter_inj : Function.Injective centerMap := by
    intro i j hij
    have hpair : (i, (1 : Fin 3)) = (j, (1 : Fin 3)) :=
      p.place.injective hij
    exact congrArg Prod.fst hpair
  let centerMap' : Fin p.blockCount → (↑C : Set V) := fun i =>
    ⟨centerMap i, by
      change centerMap i ∈ R03SP01FactorCenterSet p
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hcenter'_inj : Function.Injective centerMap' := by
    intro i j hij
    apply hcenter_inj
    exact congrArg Subtype.val hij
  have hcenter'_surj : Function.Surjective centerMap' := by
    intro x
    have hxC : (x : V) ∈ R03SP01FactorCenterSet p := x.property
    rcases Finset.mem_image.mp hxC with ⟨i, hi, hix⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hix
  let eC : Fin p.blockCount ≃ (↑C : Set V) :=
    Equiv.ofBijective centerMap' ⟨hcenter'_inj, hcenter'_surj⟩
  let leafPos : Fin 2 → Fin 3 := fun j => if j = 0 then 0 else 2
  have hleafPos_inj : Function.Injective leafPos := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [leafPos] at hjk ⊢
  let leafMap : Fin p.blockCount × Fin 2 → V := fun x =>
    p.place (x.1, leafPos x.2)
  have hleafMap_not_center (x : Fin p.blockCount × Fin 2) :
      leafMap x ∉ C := by
    rcases x with ⟨xblock, xslot⟩
    intro hx
    have hxC : leafMap (xblock, xslot) ∈ R03SP01FactorCenterSet p := hx
    rcases Finset.mem_image.mp hxC with ⟨i, hi, hix⟩
    have hpair : (i, (1 : Fin 3)) = (xblock, leafPos xslot) := by
      apply p.place.injective
      calc
        p.place (i, (1 : Fin 3)) = centerMap i := rfl
        _ = leafMap (xblock, xslot) := hix
        _ = p.place (xblock, leafPos xslot) := rfl
    have hsecond := congrArg Prod.snd hpair
    fin_cases xslot <;> simp [leafPos] at hsecond
  let leafMap' : Fin p.blockCount × Fin 2 → ((↑C : Set V)ᶜ : Set V) := fun x =>
    ⟨leafMap x, hleafMap_not_center x⟩
  have hleafMap'_inj : Function.Injective leafMap' := by
    intro x y hxy
    have hpair : (x.1, leafPos x.2) = (y.1, leafPos y.2) := by
      apply p.place.injective
      exact congrArg Subtype.val hxy
    have hfst : x.1 = y.1 :=
      congrArg (fun q : Fin p.blockCount × Fin 3 => q.1) hpair
    have hsnd : x.2 = y.2 := hleafPos_inj
      (congrArg (fun q : Fin p.blockCount × Fin 3 => q.2) hpair)
    exact Prod.ext hfst hsnd
  have hleafMap'_surj : Function.Surjective leafMap' := by
    intro z
    let x : Fin p.blockCount × Fin 3 := p.place.symm (z : V)
    have hx : p.place x = (z : V) := p.place.apply_symm_apply (z : V)
    have hxnot : x.2 ≠ (1 : Fin 3) := by
      intro hxone
      have hzC : (z : V) ∈ C := by
        change (z : V) ∈ R03SP01FactorCenterSet p
        apply Finset.mem_image.mpr
        refine ⟨x.1, Finset.mem_univ _, ?_⟩
        have hxpair : x = (x.1, (1 : Fin 3)) :=
          Prod.ext rfl hxone
        rw [← hxpair]
        simpa [centerMap] using hx
      exact z.property hzC
    let xj : Fin 3 := x.2
    have hxjval : xj.val ≠ 1 := by
      intro hv
      apply hxnot
      apply Fin.ext
      exact hv
    have hxcases : x.2 = 0 ∨ x.2 = 2 := by
      have hxcases' : xj.val = 0 ∨ xj.val = 2 := by
        omega
      rcases hxcases' with hzero | htwo
      · left
        apply Fin.ext
        exact hzero
      · right
        apply Fin.ext
        exact htwo
    rcases hxcases with hxzero | hxtwo
    · refine ⟨(x.1, (0 : Fin 2)), ?_⟩
      apply Subtype.ext
      change p.place (x.1, leafPos 0) = (z : V)
      have hxpair : x = (x.1, (0 : Fin 3)) := Prod.ext rfl hxzero
      have hx' : p.place (x.1, (0 : Fin 3)) = (z : V) := by
        rw [← hxpair]
        exact hx
      simpa [leafPos] using hx'
    · refine ⟨(x.1, (1 : Fin 2)), ?_⟩
      apply Subtype.ext
      change p.place (x.1, leafPos 1) = (z : V)
      have hxpair : x = (x.1, (2 : Fin 3)) := Prod.ext rfl hxtwo
      have hx' : p.place (x.1, (2 : Fin 3)) = (z : V) := by
        rw [← hxpair]
        exact hx
      simpa [leafPos] using hx'
  let eL : (Fin p.blockCount × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V) :=
    Equiv.ofBijective leafMap' ⟨hleafMap'_inj, hleafMap'_surj⟩
  change R03SP01CenterSlotCertificate G C
  refine ⟨p.blockCount, eC, eL, ?_⟩
  intro i j
  fin_cases j
  · change G.Adj (p.place (i, (0 : Fin 3)))
      (p.place (i, (1 : Fin 3)))
    exact p.edge01 i
  · change G.Adj (p.place (i, (2 : Fin 3)))
      (p.place (i, (1 : Fin 3)))
    exact SimpleGraph.Adj.symm (p.edge12 i)

#print axioms R03SP01FactorCenterSet
#print axioms R03SP01P3FactorCenterSlotCertificate

/-- Exact center-set reformulation with the order identity exposed.  The
forward direction takes the middle positions of a factor; the reverse
方向 uses the center-slot certificate. -/
theorem R03SP01P3FactorIffCenterSlotCertificateOfCard
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    Nonempty (P3Factor G) ↔
      ∃ C : Finset V,
        C.card * 3 = Fintype.card V ∧
        R03SP01CenterSlotCertificate G C := by
  classical
  constructor
  · rintro ⟨p⟩
    let C : Finset V := R03SP01FactorCenterSet p
    have hcenter_inj : Function.Injective
        (fun i : Fin p.blockCount => p.place (i, (1 : Fin 3))) := by
      intro i j hij
      have hpair : (i, (1 : Fin 3)) = (j, (1 : Fin 3)) :=
        p.place.injective hij
      exact congrArg Prod.fst hpair
    have hCcard : C.card = p.blockCount := by
      dsimp [C, R03SP01FactorCenterSet]
      rw [Finset.card_image_of_injective Finset.univ hcenter_inj]
      simp
    have hVcard : p.blockCount * 3 = Fintype.card V := by
      have hp := Fintype.card_congr p.place
      simpa using hp
    refine ⟨C, ?_, ?_⟩
    · rw [hCcard]
      exact hVcard
    · exact R03SP01P3FactorCenterSlotCertificate p
  · rintro ⟨C, hcard, hcert⟩
    exact R03SP01CenterSlotCertificateP3Factor G C hcert

#print axioms R03SP01P3FactorIffCenterSlotCertificateOfCard

/-- Exact Hall form of the center-set reduction.  A factor exists precisely
when some finite center set has the correct one-third cardinality and its
capacity-two slot relation satisfies Hall's inequalities. -/
theorem R03SP01P3FactorIffCenterSlotHall
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] :
    Nonempty (P3Factor G) ↔
      ∃ C : Finset V, ∃ n : Nat,
        C.card = n ∧
        n * 3 = Fintype.card V ∧
        ∃ eC : Fin n ≃ (↑C : Set V),
          R03SP01CenterSlotHallCondition G C n eC := by
  classical
  constructor
  · rintro ⟨p⟩
    let C : Finset V := R03SP01FactorCenterSet p
    have hcert : R03SP01CenterSlotCertificate G C := by
      simpa [C] using R03SP01P3FactorCenterSlotCertificate p
    rcases hcert with ⟨n, eC, eL, hAdj⟩
    let Cset : Set V := (↑C : Set V)
    letI : Fintype Cset := Fintype.ofFinite _
    letI : Fintype ((Csetᶜ : Set V)) := Fintype.ofFinite _
    have hCcard : Fintype.card Cset = C.card := by
      simp [Cset]
    have hnC : n = C.card := by
      have he := Fintype.card_congr eC
      simpa [Cset] using he
    have hfactorcard : p.blockCount * 3 = Fintype.card V := by
      simpa using (Fintype.card_congr p.place)
    have hcenter_inj : Function.Injective
        (fun i : Fin p.blockCount => p.place (i, (1 : Fin 3))) := by
      intro i j hij
      have hpair : (i, (1 : Fin 3)) = (j, (1 : Fin 3)) :=
        p.place.injective hij
      exact congrArg Prod.fst hpair
    have hCblock : C.card = p.blockCount := by
      have hcenter_inj' : Function.Injective
          (fun i : Fin p.blockCount => p.place (i, (1 : Fin 3))) := hcenter_inj
      have himage :
          (@Finset.image (Fin p.blockCount) V (Classical.decEq V)
            (fun i : Fin p.blockCount => p.place (i, (1 : Fin 3)))
            Finset.univ).card = Fintype.card (Fin p.blockCount) := by
        exact @Finset.card_image_of_injective _ _ _ (Classical.decEq V)
          Finset.univ hcenter_inj'
      simpa [C, R03SP01FactorCenterSet] using himage
    have hcardn : n * 3 = Fintype.card V := by
      omega
    have hsum : Fintype.card Cset +
        Fintype.card ((Csetᶜ : Set V)) = Fintype.card V := by
      simpa [Cset] using
        (Fintype.card_congr (Equiv.Set.sumCompl Cset))
    have hcomp : Fintype.card ((Csetᶜ : Set V)) = n * 2 := by
      omega
    have hHall : R03SP01CenterSlotHallCondition G C n eC := by
      apply (R03SP01CenterSlotCertificateAtIffHall G C n eC hcomp).mp
      exact ⟨eL, hAdj⟩
    exact ⟨C, n, hnC.symm, hcardn, eC, hHall⟩
  · rintro ⟨C, n, hCn, hcardn, eC, hHall⟩
    let Cset : Set V := (↑C : Set V)
    letI : Fintype Cset := Fintype.ofFinite _
    letI : Fintype ((Csetᶜ : Set V)) := Fintype.ofFinite _
    have hCcard : Fintype.card Cset = C.card := by
      simp [Cset]
    have hsum : Fintype.card Cset +
        Fintype.card ((Csetᶜ : Set V)) = Fintype.card V := by
      simpa [Cset] using
        (Fintype.card_congr (Equiv.Set.sumCompl Cset))
    have hcomp : Fintype.card ((Csetᶜ : Set V)) = n * 2 := by
      omega
    have hAt : R03SP01CenterSlotCertificateAt G C n eC :=
      (R03SP01CenterSlotCertificateAtIffHall G C n eC hcomp).mpr hHall
    apply R03SP01CenterSlotCertificateP3Factor G C
    exact ⟨n, eC, hAt⟩

#print axioms R03SP01P3FactorIffCenterSlotHall


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (hNo : ¬ Nonempty (P3Factor G)) :
    ∀ (C : Finset V) (n : Nat),
      C.card = n →
      n * 3 = Fintype.card V →
      ∀ eC : Fin n ≃ (↑C : Set V),
        ∃ A : Finset ((↑C : Set V)ᶜ : Set V),
          (Finset.univ.filter (fun b : Fin n × Fin 2 =>
            ∃ a ∈ A, G.Adj (a : V) (eC b.1 : V))).card < A.card := by
  classical
  intro C n hCn hcard eC
  by_contra hNoObstruction
  push_neg at hNoObstruction
  have hHall : R03SP01CenterSlotHallCondition G C n eC := by
    intro A
    have h := hNoObstruction A
    omega
  exact hNo ((R03SP01P3FactorIffCenterSlotHall G).mpr
    ⟨C, n, hCn, hcard, eC, hHall⟩)
