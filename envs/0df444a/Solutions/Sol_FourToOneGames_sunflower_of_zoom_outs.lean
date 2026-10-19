-- Prove2me | solution 1 for FourToOneGames.sunflower_of_zoom_outs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T08:02:11.205125+00:00
-- url     : https://prove2.me/submissions/0423c5ef-dfea-4834-9c7d-e5d41421871b

import Mathlib
import Definitions.Def_FourToOneGames_Grassmann

section

namespace SFAux
open Module

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] [DecidableEq E]

open Classical in
lemma card_filter_mem (U : Submodule (ZMod 2) E) :
    (Finset.univ.filter (fun x : E => x ∈ U)).card = 2 ^ finrank (ZMod 2) U := by
  classical
  rw [← Fintype.card_subtype]
  have := Module.card_eq_pow_finrank (K := ZMod 2) (V := U)
  rw [ZMod.card] at this
  convert this

lemma inf_eq_of_le (L C U : Submodule (ZMod 2) E) (hLC : IsCompl L C) (hL : L ≤ U) :
    U = L ⊔ (U ⊓ C) := by
  have h := sup_inf_assoc_of_le C hL
  rw [hLC.sup_eq_top, top_inf_eq, inf_comm] at h
  exact h

lemma finrank_inf_compl (L C U : Submodule (ZMod 2) E) (hLC : IsCompl L C) (hL : L ≤ U) :
    finrank (ZMod 2) U = finrank (ZMod 2) L + finrank (ZMod 2) ↥(U ⊓ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (U ⊓ C)
  have hb : L ⊓ (U ⊓ C) = ⊥ := by
    refine eq_bot_iff.mpr (le_trans (inf_le_inf_left L inf_le_right) ?_)
    exact hLC.inf_eq_bot.le
  rw [hb, finrank_bot, add_zero, ← inf_eq_of_le L C U hLC hL] at h
  exact h

theorem core (r : ℕ) (hr : 1 ≤ r) (m : ℕ) (hm : 1 ≤ m) :
    ∀ F : Finset (Submodule (ZMod 2) E), (∀ U ∈ F, finrank (ZMod 2) U = r) →
      (m * 2 ^ r) ^ r ≤ F.card →
      ∃ U₀ : Submodule (ZMod 2) E, ∃ s : ℕ, 0 < s ∧ s ≤ r ∧ finrank (ZMod 2) U₀ = r - s ∧
        ∃ I ⊆ F, I.card = m ∧ (∀ U ∈ I, U₀ ≤ U) ∧
          (∀ U ∈ I, ∀ U' ∈ I, U ≠ U' → U ⊓ U' = U₀) := by
  classical
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro F hF hcard
  by_cases hcase : ∃ I ⊆ F, I.card = m ∧ ∀ U ∈ I, ∀ U' ∈ I, U ≠ U' → U ⊓ U' = ⊥
  · obtain ⟨I, hIF, hIc, hI⟩ := hcase
    exact ⟨⊥, r, hr, le_rfl, by simp, I, hIF, hIc, fun _ _ => bot_le, hI⟩
  -- r ≥ 2
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hr1 : r = 1 := by omega
    apply hcase
    have hmF : m ≤ F.card := by
      calc m ≤ (m * 2 ^ r) ^ r := by
            rw [hr1, pow_one, pow_one]; omega
        _ ≤ F.card := hcard
    obtain ⟨I, hIF, hIc⟩ := Finset.exists_subset_card_eq hmF
    refine ⟨I, hIF, hIc, fun U hU U' hU' hne => ?_⟩
    by_contra hb
    have h1 : 1 ≤ finrank (ZMod 2) ↥(U ⊓ U') := by
      rw [Nat.one_le_iff_ne_zero]; intro h0
      exact hb (Submodule.finrank_eq_zero.mp h0)
    have hU1 := hF U (hIF hU); have hU1' := hF U' (hIF hU')
    have e1 : U ⊓ U' = U := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
    have e2 : U ⊓ U' = U' := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
    exact hne (e1.symm.trans e2)
  -- maximal pairwise-trivial subfamily
  set P := F.powerset.filter
    (fun G => ∀ U ∈ G, ∀ U' ∈ G, U ≠ U' → U ⊓ U' = ⊥) with hP
  have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨G, hGP, hGmax⟩ := Finset.exists_max_image P Finset.card hPne
  rw [hP, Finset.mem_filter, Finset.mem_powerset] at hGP
  obtain ⟨hGF, hGpair⟩ := hGP
  have hGm : G.card < m := by
    by_contra hge; push Not at hge
    obtain ⟨I, hIG, hIc⟩ := Finset.exists_subset_card_eq hge
    exact hcase ⟨I, hIG.trans hGF, hIc, fun U hU U' hU' => hGpair U (hIG hU) U' (hIG hU')⟩
  have hmeet : ∀ U ∈ F, ∃ j ∈ G, U ⊓ j ≠ ⊥ := by
    intro U hU
    by_cases hUG : U ∈ G
    · refine ⟨U, hUG, ?_⟩
      rw [inf_idem]; intro h0
      have := hF U hU; rw [h0, finrank_bot] at this; omega
    · by_contra hno; push Not at hno
      have hins : insert U G ∈ P := by
        rw [hP, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.insert_subset hU hGF, fun a ha b hb hab => ?_⟩
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hno b hb
        · rw [inf_comm]; exact hno a ha
        · exact hGpair a ha b hb hab
      have := hGmax _ hins
      rw [Finset.card_insert_of_notMem hUG] at this; omega
  set S : Finset E := G.biUnion (fun j => Finset.univ.filter (fun x => x ∈ j ∧ x ≠ 0)) with hS
  have hScard : S.card ≤ m * 2 ^ r := by
    calc S.card ≤ ∑ j ∈ G, (Finset.univ.filter (fun x : E => x ∈ j ∧ x ≠ 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j ∈ G, 2 ^ r := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [← hF j (hGF hj), ← card_filter_mem j]
          refine Finset.card_le_card (fun x hx => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact hx.1
      _ = G.card * 2 ^ r := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * 2 ^ r := Nat.mul_le_mul_right _ hGm.le
  have hexS : ∀ U ∈ F, ∃ x ∈ S, x ∈ U := by
    intro U hU
    obtain ⟨j, hj, hne⟩ := hmeet U hU
    obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hne
    refine ⟨x, ?_, (Submodule.mem_inf.mp hx).1⟩
    rw [hS, Finset.mem_biUnion]
    exact ⟨j, hj, by simp [(Submodule.mem_inf.mp hx).2, hx0]⟩
  set f : Submodule (ZMod 2) E → E := fun U => if h : ∃ x ∈ S, x ∈ U then h.choose else 0 with hf
  have hfS : ∀ U ∈ F, f U ∈ S ∧ f U ∈ U := by
    intro U hU
    have h := hexS U hU
    simp only [hf, dif_pos h]
    exact h.choose_spec
  have hFne : F.Nonempty := by
    rw [← Finset.card_pos]; exact lt_of_lt_of_le (by positivity) hcard
  obtain ⟨U1, hU1⟩ := hFne
  have hSne : S.Nonempty := ⟨_, (hfS U1 hU1).1⟩
  set n := (m * 2 ^ r) ^ (r - 1) with hn
  have hmul : S.card * n ≤ F.card := by
    calc S.card * n ≤ (m * 2 ^ r) * n := Nat.mul_le_mul_right _ hScard
      _ = (m * 2 ^ r) ^ r := by
          rw [hn, ← pow_succ']; congr 1; omega
      _ ≤ F.card := hcard
  obtain ⟨v, hvS, hvn⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (fun U hU => (hfS U hU).1) hSne hmul
  set Fv := F.filter (fun U => f U = v) with hFv
  have hv0 : v ≠ 0 := by
    rw [hS, Finset.mem_biUnion] at hvS
    obtain ⟨j, _, hj⟩ := hvS
    exact (Finset.mem_filter.mp hj).2.2
  have hvU : ∀ U ∈ Fv, v ∈ U := by
    intro U hU
    rw [hFv, Finset.mem_filter] at hU
    rw [← hU.2]; exact (hfS U hU.1).2
  set L : Submodule (ZMod 2) E := Submodule.span (ZMod 2) {v} with hL
  have hLU : ∀ U ∈ Fv, L ≤ U := fun U hU =>
    (Submodule.span_singleton_le_iff_mem _ _).mpr (hvU U hU)
  have hL1 : finrank (ZMod 2) L = 1 := finrank_span_singleton hv0
  obtain ⟨C, hC⟩ := L.exists_isCompl
  set φ : Submodule (ZMod 2) E → Submodule (ZMod 2) E := fun U => U ⊓ C with hφ
  have hinj : Set.InjOn φ Fv := by
    intro U hU U' hU' h
    rw [inf_eq_of_le L C U hC (hLU U hU), inf_eq_of_le L C U' hC (hLU U' hU')]
    exact congrArg (fun X => L ⊔ X) h
  set F' := Fv.image φ with hF'
  have hF'r : ∀ U ∈ F', finrank (ZMod 2) U = r - 1 := by
    intro U hU
    rw [hF', Finset.mem_image] at hU
    obtain ⟨U, hU, rfl⟩ := hU
    have := finrank_inf_compl L C U hC (hLU U hU)
    rw [hL1, hF U (Finset.mem_filter.mp hU).1] at this
    show finrank (ZMod 2) ↥(U ⊓ C) = r - 1
    omega
  have hF'card : (m * 2 ^ (r - 1)) ^ (r - 1) ≤ F'.card := by
    rw [hF', Finset.card_image_of_injOn hinj]
    refine le_trans ?_ hvn
    rw [hn]
    exact Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))) _
  obtain ⟨U₀', s, hs0, hsr, hU₀'r, I', hI'F', hI'c, hI'le, hI'pair⟩ :=
    ih (r - 1) (by omega) (by omega) F' hF'r hF'card
  set I := Fv.filter (fun U => φ U ∈ I') with hI
  have hIimg : I.image φ = I' := by
    ext W; constructor
    · intro hW
      rw [Finset.mem_image] at hW
      obtain ⟨U, hU, rfl⟩ := hW
      exact (Finset.mem_filter.mp hU).2
    · intro hW
      have := hI'F' hW
      rw [hF', Finset.mem_image] at this
      obtain ⟨U, hU, rfl⟩ := this
      exact Finset.mem_image.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hW⟩, rfl⟩
  have hIFv : I ⊆ Fv := Finset.filter_subset _ _
  have hIc : I.card = m := by
    rw [← hI'c, ← hIimg, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hIFv))]
  have hI'ne : I'.Nonempty := by rw [← Finset.card_pos, hI'c]; omega
  obtain ⟨W1, hW1⟩ := hI'ne
  have hU₀'C : U₀' ≤ C := by
    have := hI'F' hW1
    rw [hF', Finset.mem_image] at this
    obtain ⟨U, _, rfl⟩ := this
    exact (hI'le _ hW1).trans inf_le_right
  refine ⟨L ⊔ U₀', s, hs0, by omega, ?_, I, hIFv.trans (Finset.filter_subset _ _), hIc, ?_, ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq L U₀'
    have hb : L ⊓ U₀' = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left L hU₀'C).trans hC.inf_eq_bot.le)
    rw [hb, finrank_bot, add_zero, hL1, hU₀'r] at h
    omega
  · intro U hU
    have hUv := hIFv hU
    refine sup_le (hLU U hUv) ((hI'le _ (Finset.mem_filter.mp hU).2).trans inf_le_left)
  · intro U hU U' hU' hne
    have hUv := hIFv hU; have hU'v := hIFv hU'
    have hne' : φ U ≠ φ U' := fun h => hne (hinj hUv hU'v h)
    have hpair := hI'pair _ (Finset.mem_filter.mp hU).2 _ (Finset.mem_filter.mp hU').2 hne'
    have hLUU : L ≤ U ⊓ U' := le_inf (hLU U hUv) (hLU U' hU'v)
    rw [inf_eq_of_le L C (U ⊓ U') hC hLUU, ← hpair]
    congr 1
    simp only [hφ]
    rw [inf_inf_inf_comm, inf_idem]

end SFAux

end

section

namespace SFAux
open Module FourToOneGames

theorem main (n r m N : ℕ) (hr : 0 < r) (hm : 0 < m)
    (W : Fin N → Submodule (ZMod 2) (Fspace n)) (hinj : Function.Injective W)
    (hcodim : ∀ i, codim (W i) = r) (hN : (m * 2 ^ r) ^ r ≤ N) :
    ∃ (s : ℕ) (W₀ : Submodule (ZMod 2) (Fspace n)) (I : Finset (Fin N)),
      0 < s ∧ s ≤ r ∧ codim W₀ = r - s ∧ I.card = m ∧
      (∀ i ∈ I, W i ≤ W₀) ∧
      (∀ i ∈ I, relCodim W₀ (W i) = s) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → relCodim W₀ (W i ⊓ W j) = 2 * s) := by
  classical
  set D := Module.Dual (ZMod 2) (Fspace n)
  haveI : Finite D := Module.finite_of_finite (ZMod 2)
  letI : Fintype D := Fintype.ofFinite D
  have hV : finrank (ZMod 2) (Fspace n) = n := by simp
  have hann : ∀ X : Submodule (ZMod 2) (Fspace n),
      finrank (ZMod 2) X + finrank (ZMod 2) X.dualAnnihilator = n := fun X => by
    rw [Subspace.finrank_add_finrank_dualAnnihilator_eq, hV]
  have hle : ∀ X : Submodule (ZMod 2) (Fspace n), finrank (ZMod 2) X ≤ n := fun X => by
    have := hann X; omega
  have hWr : ∀ i, finrank (ZMod 2) (W i) = n - r := fun i => by
    have := hcodim i; unfold codim at this; have := hle (W i); omega
  have hrn : r ≤ n := by
    have := hcodim ⟨0, by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; have : 0 < (m * 2 ^ r) ^ r := by positivity
        omega
      · exact h⟩
    unfold codim at this; omega
  set A : Fin N → Submodule (ZMod 2) D := fun i => (W i).dualAnnihilator with hA
  have hAinj : Function.Injective A := fun i j h => hinj (Subspace.dualAnnihilator_inj.mp h)
  have hAr : ∀ i, finrank (ZMod 2) (A i) = r := fun i => by
    have := hann (W i); rw [hWr i] at this
    show finrank (ZMod 2) (W i).dualAnnihilator = r; omega
  set F := Finset.univ.image A with hF
  have hFr : ∀ U ∈ F, finrank (ZMod 2) U = r := by
    intro U hU; rw [hF, Finset.mem_image] at hU; obtain ⟨i, _, rfl⟩ := hU; exact hAr i
  have hFc : (m * 2 ^ r) ^ r ≤ F.card := by
    rw [hF, Finset.card_image_of_injective _ hAinj, Finset.card_univ, Fintype.card_fin]; exact hN
  obtain ⟨U₀, s, hs0, hsr, hU₀r, I', hI'F, hI'c, hI'le, hI'pair⟩ := core r hr m hm F hFr hFc
  set W₀ := U₀.dualCoannihilator with hW₀
  have hW₀a : W₀.dualAnnihilator = U₀ := Subspace.dualCoannihilator_dualAnnihilator_eq
  have hW₀r : finrank (ZMod 2) W₀ = n - (r - s) := by
    have := hann W₀; rw [hW₀a, hU₀r] at this; omega
  set I := Finset.univ.filter (fun i => A i ∈ I') with hI
  have hIimg : I.image A = I' := by
    ext U; constructor
    · intro hU; rw [Finset.mem_image] at hU; obtain ⟨i, hi, rfl⟩ := hU
      exact (Finset.mem_filter.mp hi).2
    · intro hU
      have := hI'F hU; rw [hF, Finset.mem_image] at this; obtain ⟨i, _, rfl⟩ := this
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩, rfl⟩
  have hIc : I.card = m := by
    rw [← hI'c, ← hIimg, Finset.card_image_of_injective _ hAinj]
  have hWle : ∀ i ∈ I, W i ≤ W₀ := by
    intro i hi
    have h := hI'le _ (Finset.mem_filter.mp hi).2
    rw [← hW₀a] at h
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp h
  refine ⟨s, W₀, I, hs0, hsr, ?_, hIc, hWle, ?_, ?_⟩
  · unfold codim; rw [hW₀r]; omega
  · intro i _; unfold relCodim; rw [hW₀r, hWr i]; omega
  · intro i hi j hj hij
    have hne : A i ≠ A j := fun h => hij (hAinj h)
    have hp := hI'pair _ (Finset.mem_filter.mp hi).2 _ (Finset.mem_filter.mp hj).2 hne
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (A i) (A j)
    rw [hp, hU₀r, hAr i, hAr j] at hsup
    have hinf : (W i ⊓ W j).dualAnnihilator = A i ⊔ A j := Subspace.dualAnnihilator_inf_eq _ _
    have h2 := hann (W i ⊓ W j)
    rw [hinf] at h2
    have hg : finrank (ZMod 2) ↥(A i ⊔ A j) = r + s := by omega
    rw [hg] at h2
    unfold relCodim; rw [hW₀r]
    omega

end SFAux

end

open FourToOneGames in
theorem solution (n r m N : ℕ) (hr : 0 < r) (hm : 0 < m)
    (W : Fin N → Submodule (ZMod 2) (Fspace n)) (hinj : Function.Injective W)
    (hcodim : ∀ i, codim (W i) = r) (hN : (m * 2 ^ r) ^ r ≤ N) :
    ∃ (s : ℕ) (W₀ : Submodule (ZMod 2) (Fspace n)) (I : Finset (Fin N)),
      0 < s ∧ s ≤ r ∧ codim W₀ = r - s ∧ I.card = m ∧
      (∀ i ∈ I, W i ≤ W₀) ∧
      (∀ i ∈ I, relCodim W₀ (W i) = s) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → relCodim W₀ (W i ⊓ W j) = 2 * s) :=
  SFAux.main n r m N hr hm W hinj hcodim hN
