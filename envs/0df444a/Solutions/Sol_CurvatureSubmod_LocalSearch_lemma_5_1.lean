-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T03:12:20.929724+00:00
-- url     : https://prove2.me/submissions/32f5c993-1317-4176-bb9d-c079b0312798

/-
Brualdi's bijective base exchange, 23 October 2026.
Original mathematical attribution: Richard A. Brualdi (1969), as cited in
Sviridenko, Vondrak and Ward, arXiv:1311.4728v2, Lemma 5.1, printed p.6.
The pinned v2 PDF and its Brualdi reference were inspected; the original 1969
paper was not inspected. The v2 PDF displays a 2019 title date despite the
2014 arXiv version date. No new mathematical discovery is claimed.
New formalization: Hall's condition follows from spanning by fundamental
circuit neighbors and matroid rank. A matching between equal-sized bases is
inverted to give the required exchange bijection, including common elements.
Alexander Richard Towell directed the work; OpenAI Codex substantially
constructed and verified the proof. mikedeng1 supplied the formal target;
Shuze Chen confirmed its statement, not this proof. Mathlib contributors
supply Hall's theorem and the matroid foundations. No prior platform proof
is reused and no independent human review is claimed.
-/
import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

open Set Matroid
open scoped Classical
set_option autoImplicit false

namespace ExchangeResearch

lemma mem_closure_neighbors {X : Type*} (M : Matroid X) (A : Set X)
    (hA : M.IsBase A) (b : X) (hb : b ∈ M.E) :
    b ∈ M.closure (M.fundCircuit b A ∩ A) := by
  by_cases hbA : b ∈ A
  · exact M.subset_closure _ (inter_subset_right.trans hA.subset_ground)
      ⟨M.mem_fundCircuit b A,hbA⟩
  · have hc := hA.fundCircuit_isCircuit hb hbA
    apply M.closure_subset_closure (X := M.fundCircuit b A \ {b}) _
      (hc.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit b A))
    intro z hz
    refine ⟨hz.1,?_⟩
    rcases M.fundCircuit_subset_insert b A hz.1 with he | hzA
    · exact False.elim (hz.2 he)
    · exact hzA

lemma neighbor_exchange {X : Type*} [DecidableEq X] (M : Matroid X) (A : Finset X)
    (hA : M.IsBase (A : Set X)) (b x : X) (hb : b ∈ M.E) (hx : x ∈ A)
    (hxc : x ∈ M.fundCircuit b (A : Set X)) :
    M.IsBase (↑(insert b (A.erase x)) : Set X) := by
  by_cases hbA : b ∈ (A : Set X)
  · have he : x=b := by simpa [M.fundCircuit_eq_of_mem hbA] using hxc
    subst x
    simpa only [Finset.insert_erase hbA] using hA
  · have hc : b ∈ M.closure (A : Set X) := by rw [hA.closure_eq]; exact hb
    have hi := (hA.indep.mem_fundCircuit_iff hc hbA).mp hxc
    have he := hA.exchange_isBase_of_indep' hx hbA hi
    have hbx : b ≠ x := by intro h; subst b; exact hbA hx
    rw [← Set.insert_sdiff_singleton_comm hbx] at he
    simpa only [Finset.coe_insert,Finset.coe_erase] using he

lemma hall_condition {X : Type} [Fintype X] [DecidableEq X] (M : Matroid X)
    (A B : Finset X) (hA : M.IsBase (A : Set X)) (hB : M.IsBase (B : Set X)) :
    ∀ s : Finset {b // b ∈ B}, s.card ≤
      (s.biUnion (fun b => (Finset.univ : Finset {a // a ∈ A}).filter
        (fun a => a.val ∈ M.fundCircuit b.val (A : Set X)))).card := by
  classical
  intro s
  let t : {b // b ∈ B} → Finset {a // a ∈ A} := fun b => Finset.univ.filter
    (fun a => a.val ∈ M.fundCircuit b.val (A : Set X))
  let C : Finset X := s.image Subtype.val
  let D : Finset X := (s.biUnion t).image Subtype.val
  have hC : M.Indep (C : Set X) := by
    apply hB.indep.subset
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact b.property
  have hspan : (C : Set X) ⊆ M.closure (D : Set X) := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    apply M.closure_subset_closure _ (mem_closure_neighbors M (A : Set X) hA b.val
      (hB.subset_ground b.property))
    intro a ha
    apply Finset.mem_image.mpr
    refine ⟨⟨a,ha.2⟩,?_,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨b,hb,by simp [t,ha.1]⟩
  have hr : (C : Set X).encard ≤ (D : Set X).encard := by
    calc
      (C : Set X).encard ≤ M.eRk (M.closure (D : Set X)) := hC.encard_le_eRk_of_subset hspan
      _ = M.eRk (D : Set X) := M.eRk_closure_eq _
      _ ≤ (D : Set X).encard := M.eRk_le_encard _
  have hCcard : C.card = s.card := Finset.card_image_iff.mpr
    (fun a _ b _ h => Subtype.ext h)
  have hDcard : D.card = (s.biUnion t).card := Finset.card_image_iff.mpr
    (fun a _ b _ h => Subtype.ext h)
  have hcard : C.card ≤ D.card := by exact_mod_cast hr
  rw [hCcard,hDcard] at hcard
  exact hcard

end ExchangeResearch

theorem solution {X : Type} [Fintype X] [DecidableEq X] (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X)) :
    ∃ π : X → X, Set.BijOn π (↑A : Set X) (↑B : Set X) ∧
      ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X) := by
  classical
  let t : {b // b ∈ B} → Finset {a // a ∈ A} := fun b => Finset.univ.filter
    (fun a => a.val ∈ M.fundCircuit b.val (A : Set X))
  obtain ⟨f,hfinj,hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp
    (ExchangeResearch.hall_condition M A B hA hB)
  have hc : Fintype.card {b // b ∈ B} = Fintype.card {a // a ∈ A} := by
    simpa using hB.ncard_eq_ncard_of_isBase hA
  have hfbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj,hc⟩
  let e : {b // b ∈ B} ≃ {a // a ∈ A} := Equiv.ofBijective f hfbij
  let π : X → X := fun x => if hx : x ∈ A then (e.symm ⟨x,hx⟩).val else x
  have hp : ∀ x (hx : x ∈ A), π x = (e.symm ⟨x,hx⟩).val := by
    intro x hx; simp [π,hx]
  refine ⟨π,⟨?_,?_,?_⟩,?_⟩
  · intro x hx
    rw [hp x hx]
    exact (e.symm ⟨x,hx⟩).property
  · intro x hx y hy h
    rw [hp x hx,hp y hy] at h
    have hh := e.symm.injective (Subtype.ext h)
    exact congrArg Subtype.val hh
  · intro b hb
    refine ⟨(e ⟨b,hb⟩).val,(e ⟨b,hb⟩).property,?_⟩
    rw [hp _ (e ⟨b,hb⟩).property]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨b,hb⟩)
  · intro x hx
    rw [hp x hx]
    apply ExchangeResearch.neighbor_exchange M A hA _ x
      (hB.subset_ground (e.symm ⟨x,hx⟩).property) hx
    have hh := hfmem (e.symm ⟨x,hx⟩)
    have he : f (e.symm ⟨x,hx⟩) = ⟨x,hx⟩ := e.apply_symm_apply ⟨x,hx⟩
    simpa [t,he] using hh
#print axioms solution
