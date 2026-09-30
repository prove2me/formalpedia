-- Prove2me | solution 1 for ComputationalLearning.sauer_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:43:02.850317+00:00
-- url     : https://prove2.me/submissions/e0973319-4424-46ef-9e9b-489e5b1796f3

import Mathlib
import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

lemma phi_closed (d m : ℕ) : Phi d m = ∑ i ∈ Finset.range (d + 1), m.choose i := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => simp [Phi]
    | succ d => simp [Phi, Finset.sum_range_succ']
  | succ m ih =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      rw [show Phi (d + 1) (m + 1) = Phi (d + 1) m + Phi d m from rfl, ih (d + 1), ih d]
      rw [Finset.sum_range_succ' (fun i => (m + 1).choose i),
        Finset.sum_range_succ' (fun i => m.choose i) (d + 1)]
      simp only [Nat.choose_succ_succ, Finset.sum_add_distrib, Nat.choose_zero_right]
      ring

theorem sauer_main {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (d : ℕ)
    (hd : vcDim C ≤ d) (m : ℕ) : growth C m ≤ Phi d m := by
  classical
  unfold growth
  refine ciSup_le' fun S => ciSup_le' fun hS => ?_
  set F := restrictions C S with hF
  let tset : (S → Bool) → Finset S := fun f => Finset.univ.filter (fun x => f x = true)
  have hinj : Function.Injective tset := by
    intro f g hfg
    funext x
    have hx := congrArg (fun s : Finset S => x ∈ s) hfg
    simp only [tset, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hx
    exact Bool.eq_iff_iff.mpr hx
  set 𝒜 : Finset (Finset S) := F.toFinset.image tset with h𝒜
  have hcard : F.ncard = 𝒜.card := by
    rw [h𝒜, Finset.card_image_of_injective _ hinj, Set.ncard_eq_toFinset_card']
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro t ht
    rw [Finset.mem_shatterer] at ht
    set T : Finset X := t.map (Function.Embedding.subtype _) with hT
    have hsh : Shatters C T := by
      intro f
      set u : Finset S := t.filter (fun y => if h : y ∈ t then
        f ⟨y.1, Finset.mem_map_of_mem (Function.Embedding.subtype _) h⟩ = true else False) with hu
      have hut : u ⊆ t := by rw [hu]; exact Finset.filter_subset _ t
      obtain ⟨v, hv𝒜, hvu⟩ := ht hut
      obtain ⟨g, hgF, rfl⟩ := Finset.mem_image.mp hv𝒜
      rw [Set.mem_toFinset] at hgF
      obtain ⟨c, hcC, hcg⟩ := hgF
      refine ⟨c, hcC, ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨y, hyt, rfl⟩ := Finset.mem_map.mp hx
      have key : y ∈ t ∩ tset g ↔ y ∈ u := by rw [hvu]
      simp only [Finset.mem_inter, tset, Finset.mem_filter, Finset.mem_univ, true_and, hu,
        dif_pos hyt] at key
      have hgy : g y = true ↔ f ⟨y.1, hx⟩ = true := by
        constructor
        · intro h; exact (key.mp ⟨hyt, h⟩).2
        · intro h; exact (key.mpr ⟨hyt, h⟩).2
      show c y.1 = f ⟨y.1, hx⟩
      rw [← hcg y]
      exact Bool.eq_iff_iff.mpr hgy
    have h1 : (T.card : ℕ∞) ≤ vcDim C :=
      le_iSup₂ (f := fun (S : Finset X) (_ : Shatters C S) => (S.card : ℕ∞)) T hsh
    have h2 : T.card = t.card := Finset.card_map _
    have h3 : (t.card : ℕ∞) ≤ d := by rw [← h2]; exact h1.trans hd
    exact_mod_cast h3
  calc F.ncard = 𝒜.card := hcard
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card S).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card S).choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)
    _ = Phi d m := by
        rw [phi_closed, Fintype.card_coe, hS]
        congr 1
        ext k
        simp

end ComputationalLearning

open ComputationalLearning

theorem solution {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (d : ℕ)
    (hd : vcDim C ≤ d) (m : ℕ) :
    growth C m ≤ Phi d m := by
  exact sauer_main C d hd m
