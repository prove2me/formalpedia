-- Prove2me | solution 1 for BhangaleHypergraph.Main.avoiding_amplification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:34:43.22907+00:00
-- url     : https://prove2.me/submissions/421cc997-4b93-4c3c-9a9a-c2c3aee0c1e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BhangaleHypergraph_Main_Restricted
import Theorems.Thm_BhangaleHypergraph_Main_schrijver_chromatic
import Theorems.Thm_BhangaleHypergraph_Main_categorical_product

open BhangaleHypergraph.Main

private def coreHeight (C m : ℕ) : ℕ := (m - C + 1) / 2

private lemma coreHeight_bounds {C m : ℕ} (hC : 2 ≤ C) (hCm : C < m) :
    1 ≤ coreHeight C m ∧ 2 * coreHeight C m ≤ m ∧
      C - 1 ≤ m - 2 * coreHeight C m ∧ m - 2 * coreHeight C m ≤ C ∧
      C < m - 2 * coreHeight C m + 2 := by
  unfold coreHeight
  omega

private lemma core_mem_schrijver {C s R : ℕ} (P A H : Finset (Fin R))
    (hP : P.card ≤ (C + 1) * s + 0) (hA : A ⊆ P)
    (hsize : C < (Finset.univ \ P).card)
    (hcard : H.card = coreHeight C (Finset.univ \ P).card)
    (hstable : StableOn (Finset.univ \ P) H) :
    A ∪ H ∈ Core C s R := by
  simp only [Core, Finset.mem_filter, Finset.mem_univ, true_and]
  right
  right
  refine ⟨P, by omega, A, hA, H, rfl, ?_⟩
  simp only [if_pos hsize]
  exact ⟨hcard, hstable⟩

private lemma core_mem_smallResidual {C s R : ℕ} (P A : Finset (Fin R))
    (hP : P.card ≤ (C + 1) * s) (hA : A ⊆ P)
    (hsize : (Finset.univ \ P).card ≤ C) :
    A ∈ Core C s R := by
  simp only [Core, Finset.mem_filter, Finset.mem_univ, true_and]
  right
  right
  refine ⟨P, hP, A, hA, ∅, by simp, ?_⟩
  simp [if_neg (not_lt_of_ge hsize)]

private lemma core_mem_univ (C s R : ℕ) :
    (Finset.univ : Finset (Fin R)) ∈ Core C s R := by
  simp only [Core, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr (Or.inl (by simp))

private lemma exists_adj_eq_of_not_colorable {V : Type*} (G : SimpleGraph V) (C : ℕ)
    (κ : V → Fin C) (hnot : ¬ G.Colorable C) :
    ∃ v w, G.Adj v w ∧ κ v = κ w := by
  by_contra hn
  push_neg at hn
  exact hnot ⟨SimpleGraph.Coloring.mk κ (fun hadj => hn _ _ hadj)⟩

private lemma schrijver_not_colorable {C m : ℕ} (hC : 2 ≤ C) (hCm : C < m) :
    ¬ (Schrijver m (coreHeight C m)).Colorable C := by
  obtain ⟨hh, h2h, hdlo, hdhi, hdC⟩ := coreHeight_bounds hC hCm
  intro hc
  have hle := hc.chromaticNumber_le
  rw [schrijver_chromatic m (coreHeight C m) hh h2h] at hle
  have : (m - 2 * coreHeight C m + 2 : ℕ) ≤ C := by exact_mod_cast hle
  omega

private lemma booleanNAE_sdiff {R : ℕ} (A B X : Finset (Fin R))
    (hdisj : Disjoint A B) (hX : Finset.univ \ (A ∪ B) ⊆ X) :
    BooleanNAE A B X := by
  constructor
  · ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hxA : x ∈ A
    · exact Or.inl (Or.inl hxA)
    by_cases hxB : x ∈ B
    · exact Or.inl (Or.inr hxB)
    · exact Or.inr (hX (by simp [hxA, hxB]))
  · ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hxA, hxB⟩, hxX⟩
      exact (Finset.disjoint_left.mp hdisj hxA hxB).elim
    · intro hx
      simp at hx

private lemma avoiding_first (C s R : ℕ) (hC : 2 ≤ C) (hR : 1 ≤ R)
    (W : Finset (Finset (Fin R))) (hcore : Core C s R ⊆ W) (f : W → Fin C)
    (hf : Admissible f) :
    ∃ S : Finset (Fin R), S.Nonempty ∧ S.card ≤ C ∧ AvoidsNumber f S 1 := by
  classical
  haveI : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  by_cases hRC : R ≤ C
  · let U : W := ⟨Finset.univ, hcore (core_mem_univ C s R)⟩
    letI : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
    obtain ⟨b, hb⟩ := exists_ne (f U)
    refine ⟨Finset.univ, Finset.univ_nonempty, ?_, {b}, by simp, ?_⟩
    · simpa using hRC
    · intro X hX
      have hXU : (X : Finset (Fin R)) = Finset.univ :=
        Finset.Subset.antisymm (Finset.subset_univ _) hX
      have hUX : U = X := Subtype.ext hXU.symm
      simp only [Finset.mem_singleton]
      rw [← hUX]
      exact Ne.symm hb
  · have hCR : C < R := by omega
    let h := coreHeight C R
    obtain ⟨hh, h2h, hdlo, hdhi, hdC⟩ := coreHeight_bounds hC hCR
    have hmem (H : SchrijverVertex R h) : H.val ∈ W := by
      apply hcore
      have hc := core_mem_schrijver (C := C) (s := s) (R := R)
        (∅ : Finset (Fin R)) ∅ H.val
        (by simp) (by simp) (by simpa using hCR) (by simpa [h] using H.property.1)
        (by simpa using H.property.2)
      simpa using hc
    let κ : SchrijverVertex R h → Fin C := fun H => f ⟨H.val, hmem H⟩
    obtain ⟨H, K, hHK, hcol⟩ :=
      exists_adj_eq_of_not_colorable (Schrijver R h) C κ (schrijver_not_colorable hC hCR)
    let b : Fin C := κ H
    let S : Finset (Fin R) := Finset.univ \ (H.val ∪ K.val)
    have hdisj : Disjoint H.val K.val := hHK.2
    have hcardHK : (H.val ∪ K.val).card = 2 * h := by
      rw [Finset.card_union_of_disjoint hdisj, H.property.1, K.property.1]
      omega
    have hScard : S.card = R - 2 * h := by
      simp only [S, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, hcardHK]
    refine ⟨S, ?_, ?_, {b}, by simp, ?_⟩
    · apply Finset.card_pos.mp
      rw [hScard]
      omega
    · rw [hScard]
      exact hdhi
    · intro X hX
      simp only [Finset.mem_singleton]
      intro hXb
      have hnae : BooleanNAE H.val K.val X := booleanNAE_sdiff _ _ _ hdisj hX
      exact hf ⟨H.val, hmem H⟩ ⟨K.val, hmem K⟩ X hnae
        ⟨hcol, hcol.symm.trans hXb.symm⟩

private lemma index_pair_data {C : ℕ} (i j : Fin (C + 1)) (hij : i ≠ j) :
    (((Finset.univ.erase i).erase j).card = C - 1) ∧
      (((Finset.univ.erase i).erase j).Nonempty ↔ 2 ≤ C) := by
  have hjmem : j ∈ Finset.univ.erase i := by simp [hij.symm]
  have himem : i ∈ (Finset.univ : Finset (Fin (C + 1))) := Finset.mem_univ _
  have hcard : ((Finset.univ.erase i).erase j).card = C - 1 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem himem]
    simp
  refine ⟨hcard, ?_⟩
  rw [← Finset.card_pos, hcard]
  omega

private lemma avoiding_second_small (C s R : ℕ) (hC : 2 ≤ C)
    (W : Finset (Finset (Fin R))) (hcore : Core C s R ⊆ W) (f : W → Fin C)
    (hf : Admissible f) (T : Finset (Fin C)) (S : Fin (C + 1) → Finset (Fin R))
    (hT : T.card ≤ C - 1) (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hS : ∀ i, (S i).card ≤ s ∧ Avoids f (S i) T)
    (P Z : Finset (Fin R)) (hP : P = Finset.univ.biUnion S)
    (hZ : Z = Finset.univ \ P) (hPcard : P.card ≤ (C + 1) * s)
    (hZcard : Z.card ≤ C) :
    ∃ (b : Fin C) (U : Finset (Fin R)), b ∉ T ∧ U.card ≤ (C - 1) * s + C ∧
      Avoids f U (insert b T) := by
  classical
  have hSP (i : Fin (C + 1)) : S i ⊆ P := by
    rw [hP]
    exact Finset.subset_biUnion_of_mem S (Finset.mem_univ i)
  have hmem (i : Fin (C + 1)) : S i ∈ W := by
    apply hcore
    apply core_mem_smallResidual P (S i) hPcard (hSP i)
    simpa [hZ] using hZcard
  let κ : Fin (C + 1) → Fin C := fun i => f ⟨S i, hmem i⟩
  have hninj : ¬ Function.Injective κ := by
    intro hinj
    have hc := Fintype.card_le_of_injective κ hinj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i, j, hcol, hij⟩ := Function.not_injective_iff.mp hninj
  let b : Fin C := κ i
  let U : Finset (Fin R) := Finset.univ \ (S i ∪ S j)
  let K : Finset (Fin (C + 1)) := (Finset.univ.erase i).erase j
  let Q : Finset (Fin R) := K.biUnion S
  have hKdata := index_pair_data i j hij
  have hKcard : K.card = C - 1 := hKdata.1
  have hKne : K.Nonempty := by
    rw [← Finset.card_pos, hKcard]
    omega
  have hQcard : Q.card ≤ (C - 1) * s := by
    dsimp [Q]
    rw [Finset.card_biUnion]
    · calc
        ∑ k ∈ K, (S k).card ≤ ∑ _k ∈ K, s :=
          Finset.sum_le_sum fun k _ => (hS k).1
        _ = (C - 1) * s := by simp [hKcard]
    · intro k _ l _ hkl
      exact hdisj k l hkl
  have hQsubU : Q ⊆ U := by
    intro x hx
    obtain ⟨k, hkK, hxk⟩ := Finset.mem_biUnion.mp hx
    have hki : k ≠ i := by
      have := (Finset.mem_erase.mp (Finset.mem_erase.mp hkK).2).1
      exact this
    have hkj : k ≠ j := (Finset.mem_erase.mp hkK).1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_union, not_or]
    exact ⟨fun hxi => Finset.disjoint_left.mp (hdisj k i hki) hxk hxi,
      fun hxj => Finset.disjoint_left.mp (hdisj k j hkj) hxk hxj⟩
  have hUsub : U ⊆ Q ∪ Z := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [hP] at hxP
      obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hxP
      have hxi : x ∉ S i := by
        intro hxi
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hxi)
      have hxj : x ∉ S j := by
        intro hxj
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ hxj)
      have hki : k ≠ i := by rintro rfl; exact hxi hxk
      have hkj : k ≠ j := by rintro rfl; exact hxj hxk
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨k, by simp [K, hki, hkj], hxk⟩
    · apply Finset.mem_union_right
      simp [hZ, hxP]
  have hcard : U.card ≤ (C - 1) * s + C := by
    calc
      U.card ≤ (Q ∪ Z).card := Finset.card_le_card hUsub
      _ ≤ Q.card + Z.card := Finset.card_union_le _ _
      _ ≤ (C - 1) * s + C := Nat.add_le_add hQcard hZcard
  have hbT : b ∉ T := by
    intro hb
    exact (hS i).2 ⟨S i, hmem i⟩ (Finset.Subset.refl _) (by simpa [b, κ] using hb)
  refine ⟨b, U, hbT, hcard, ?_⟩
  intro X hX
  simp only [Finset.mem_insert, not_or]
  constructor
  · intro hXb
    have hnae : BooleanNAE (S i) (S j) X :=
      booleanNAE_sdiff _ _ _ (hdisj i j hij) hX
    apply hf ⟨S i, hmem i⟩ ⟨S j, hmem j⟩ X hnae
    constructor
    · exact hcol
    · change κ j = f X
      calc
        κ j = κ i := hcol.symm
        _ = b := rfl
        _ = f X := hXb.symm
  · obtain ⟨k, hk⟩ := hKne
    have hkU : S k ⊆ U := by
      intro x hxk
      apply hQsubU
      exact Finset.mem_biUnion.mpr ⟨k, hk, hxk⟩
    exact (hS k).2 X (hkU.trans hX)

private noncomputable def residualLift {R : ℕ} (Z : Finset (Fin R)) (i : Fin Z.card) : Fin R :=
  Z.orderEmbOfFin rfl i

private lemma sort_univ_getElem {m : ℕ} (i : Fin m) :
    (Finset.univ.sort (· ≤ ·))[i.val]? = some i := by
  classical
  have hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  let e := (Finset.univ : Finset (Fin m)).orderEmbOfFin hcard
  let E : Fin m ≃ Fin m := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  have hinv : StrictMono E.symm := by
    intro a b hab
    by_contra hn
    have hle : E.symm b ≤ E.symm a := le_of_not_gt hn
    have hba : b ≤ a := by
      have hh : e (E.symm b) ≤ e (E.symm a) := e.monotone hle
      change E (E.symm b) ≤ E (E.symm a) at hh
      simpa using hh
    exact (not_le_of_gt hab) hba
  have he : e i = i := by
    apply Fin.ext
    apply Nat.le_antisymm
    · have hh : e i ≤ E.symm (e i) := hinv.le_apply
      have heE : E i = e i := rfl
      rw [← heE] at hh
      simp only [E.symm_apply_apply] at hh
      change (E i).val ≤ i.val at hh
      exact hh
    · have hh := StrictMono.le_apply (f := (e : Fin m → Fin m)) e.strictMono (x := i)
      change i.val ≤ (e i).val at hh
      exact hh
  have hi : i.val < (Finset.univ.sort ((· ≤ ·) : Fin m → Fin m → Prop)).length := by
    rw [Finset.length_sort]
    simpa using i.isLt
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hi, ?_⟩
  change (Finset.univ.sort (· ≤ ·))[i.val] = i
  rw [show (Finset.univ.sort (· ≤ ·))[i.val] = e i by rfl]
  exact he

private lemma cyclicNext_residualLift {R : ℕ} (Z : Finset (Fin R))
    (a b : Fin Z.card) (h : CyclicNext Z (residualLift Z a) (residualLift Z b)) :
    CyclicNext Finset.univ a b := by
  classical
  rcases h with ⟨i, hi, hia, hib⟩
  obtain ⟨hi'', hval⟩ := List.getElem?_eq_some_iff.mp hia
  let iFin : Fin Z.card := ⟨i, hi⟩
  have hiFin : iFin = a := by
    apply (Z.orderEmbOfFin rfl).injective
    change residualLift Z iFin = residualLift Z a
    rw [residualLift, residualLift, Finset.orderEmbOfFin_apply,
      Finset.orderEmbOfFin_apply]
    exact hval
  have hia' : a.val = i := congrArg Fin.val hiFin.symm
  have hm : 0 < Z.card := lt_of_le_of_lt (Nat.zero_le i) hi
  let j : ℕ := (i + 1) % Z.card
  have hj : j < Z.card := Nat.mod_lt _ hm
  obtain ⟨hj'', hvalj⟩ := List.getElem?_eq_some_iff.mp
    (show (Z.sort (· ≤ ·))[j]? = some (residualLift Z b) by simpa [j] using hib)
  let jFin : Fin Z.card := ⟨j, hj⟩
  have hjFin : jFin = b := by
    apply (Z.orderEmbOfFin rfl).injective
    change residualLift Z jFin = residualLift Z b
    rw [residualLift, residualLift, Finset.orderEmbOfFin_apply,
      Finset.orderEmbOfFin_apply]
    exact hvalj
  have hb : b.val = (a.val + 1) % Z.card := by
    rw [hia']
    exact congrArg Fin.val hjFin.symm
  simp only [CyclicNext, Finset.card_univ, Fintype.card_fin]
  refine ⟨a.val, a.isLt, sort_univ_getElem a, ?_⟩
  rw [show (a.val + 1) % Z.card = b.val from hb.symm]
  exact sort_univ_getElem b

private lemma residualLift_mem {R : ℕ} (Z : Finset (Fin R)) (i : Fin Z.card) :
    residualLift Z i ∈ Z := by
  exact Z.orderEmbOfFin_mem rfl i

private lemma residualLift_injective {R : ℕ} (Z : Finset (Fin R)) :
    Function.Injective (residualLift Z) := by
  exact (Z.orderEmbOfFin rfl).injective

private def ResidualVertex {R : ℕ} (Z : Finset (Fin R)) (h : ℕ) :=
  {H : Finset (Fin R) // H.card = h ∧ StableOn Z H}

private def ResidualGraph {R : ℕ} (Z : Finset (Fin R)) (h : ℕ) :
    SimpleGraph (ResidualVertex Z h) where
  Adj A B := A ≠ B ∧ Disjoint A.val B.val
  symm := ⟨by intro A B hab; exact ⟨hab.1.symm, hab.2.symm⟩⟩
  loopless := ⟨by intro A h; exact h.1 rfl⟩

private noncomputable def schrijverResidualMap {R : ℕ} (Z : Finset (Fin R)) (h : ℕ)
    (B : SchrijverVertex Z.card h) : ResidualVertex Z h := by
  classical
  let emb : Fin Z.card ↪ Fin R := ⟨residualLift Z, residualLift_injective Z⟩
  let A : Finset (Fin R) := B.val.map emb
  have hAsub : A ⊆ Z := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact residualLift_mem Z i
  have hAcard : A.card = h := by simpa [A] using B.property.1
  have hAstable : StableOn Z A := by
    refine ⟨hAsub, ?_⟩
    intro x hx y hy hxy hnext
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact B.property.2.2 a ha b hb (by intro hab; apply hxy; rw [hab])
      (cyclicNext_residualLift Z a b hnext)
  exact ⟨A, hAcard, hAstable⟩

private lemma schrijverResidualMap_injective {R : ℕ} (Z : Finset (Fin R)) (h : ℕ) :
    Function.Injective (schrijverResidualMap Z h) := by
  classical
  intro B D heq
  apply Subtype.ext
  have hv := congrArg Subtype.val heq
  simp only [schrijverResidualMap] at hv
  exact Finset.map_injective _ hv

private lemma schrijverResidualMap_adj {R : ℕ} (Z : Finset (Fin R)) (h : ℕ)
    {B D : SchrijverVertex Z.card h} (hBD : (Schrijver Z.card h).Adj B D) :
    (ResidualGraph Z h).Adj (schrijverResidualMap Z h B) (schrijverResidualMap Z h D) := by
  classical
  refine ⟨fun heq => hBD.1 (schrijverResidualMap_injective Z h heq), ?_⟩
  rw [Finset.disjoint_left]
  intro x hxB hxD
  simp only [schrijverResidualMap] at hxB hxD
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hxB
  obtain ⟨d, hd, heq⟩ := Finset.mem_map.mp hxD
  have hbd : b = d := residualLift_injective Z
    (show residualLift Z b = residualLift Z d from heq.symm)
  subst d
  exact (Finset.disjoint_left.mp hBD.2) hb hd

private lemma not_colorable_of_chromatic_gt {V : Type} (G : SimpleGraph V) (C d : ℕ)
    (hchi : G.chromaticNumber = (d : ℕ∞)) (hd : C < d) : ¬ G.Colorable C := by
  intro hc
  have hle := hc.chromaticNumber_le
  rw [hchi] at hle
  have : d ≤ C := by exact_mod_cast hle
  omega

private lemma residual_not_colorable {R : ℕ} (Z : Finset (Fin R)) (C h : ℕ)
    (hh : 1 ≤ h) (hm : 2 * h ≤ Z.card) (hd : C < Z.card - 2 * h + 2) :
    ¬ (ResidualGraph Z h).Colorable C := by
  have hs : ¬ (Schrijver Z.card h).Colorable C :=
    not_colorable_of_chromatic_gt _ _ _ (schrijver_chromatic Z.card h hh hm) hd
  intro hc
  rcases hc with ⟨κ⟩
  apply hs
  refine ⟨SimpleGraph.Coloring.mk (fun B => κ (schrijverResidualMap Z h B)) ?_⟩
  intro B D hBD
  exact κ.valid (schrijverResidualMap_adj Z h hBD)

private lemma avoiding_second_large (C s R : ℕ) (hC : 2 ≤ C)
    (W : Finset (Finset (Fin R))) (hcore : Core C s R ⊆ W) (f : W → Fin C)
    (hf : Admissible f) (T : Finset (Fin C)) (S : Fin (C + 1) → Finset (Fin R))
    (hT : T.card ≤ C - 1) (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hS : ∀ i, (S i).card ≤ s ∧ Avoids f (S i) T)
    (P Z : Finset (Fin R)) (hP : P = Finset.univ.biUnion S)
    (hZ : Z = Finset.univ \ P) (hPcard : P.card ≤ (C + 1) * s)
    (hZcard : C < Z.card) :
    ∃ (b : Fin C) (U : Finset (Fin R)), b ∉ T ∧ U.card ≤ (C - 1) * s + C ∧
      Avoids f U (insert b T) := by
  classical
  let h := coreHeight C Z.card
  obtain ⟨hh, h2h, hdlo, hdhi, hdC⟩ := coreHeight_bounds hC hZcard
  have hSP (i : Fin (C + 1)) : S i ⊆ P := by
    rw [hP]
    exact Finset.subset_biUnion_of_mem S (Finset.mem_univ i)
  have hmem (i : Fin (C + 1)) (H : ResidualVertex Z h) : S i ∪ H.val ∈ W := by
    apply hcore
    apply core_mem_schrijver P (S i) H.val (by omega) (hSP i)
    · simpa [hZ] using hZcard
    · rw [← hZ]
      exact H.property.1
    · rw [← hZ]
      exact H.property.2
  let κ : ResidualVertex Z h × Fin (C + 1) → Fin C :=
    fun v => f ⟨S v.2 ∪ v.1.val, hmem v.2 v.1⟩
  have hnres : ¬ (ResidualGraph Z h).Colorable C := by
    apply residual_not_colorable Z C h
    · exact hh
    · exact h2h
    · exact hdC
  have hnprod : ¬ (ProductComplete (ResidualGraph Z h) C).Colorable C :=
    categorical_product _ _ hnres
  obtain ⟨⟨H, i⟩, ⟨K, j⟩, hadj, hcol⟩ :=
    exists_adj_eq_of_not_colorable (ProductComplete (ResidualGraph Z h) C) C κ hnprod
  have hij : i ≠ j := hadj.2
  let A : Finset (Fin R) := S i ∪ H.val
  let B : Finset (Fin R) := S j ∪ K.val
  have hHZ : H.val ⊆ Z := H.property.2.1
  have hKZ : K.val ⊆ Z := K.property.2.1
  have hZdisjP : Disjoint Z P := by
    rw [hZ]
    exact Finset.sdiff_disjoint
  have hA : A ∈ W := by simpa [A] using hmem i H
  have hB : B ∈ W := by simpa [B] using hmem j K
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rcases Finset.mem_union.mp hxA with hxSi | hxH
    · rcases Finset.mem_union.mp hxB with hxSj | hxK
      · exact Finset.disjoint_left.mp (hdisj i j hij) hxSi hxSj
      · have hxP : x ∈ P := hSP i hxSi
        exact Finset.disjoint_left.mp hZdisjP (hKZ hxK) hxP
    · rcases Finset.mem_union.mp hxB with hxSj | hxK
      · have hxP : x ∈ P := hSP j hxSj
        exact Finset.disjoint_left.mp hZdisjP (hHZ hxH) hxP
      · exact Finset.disjoint_left.mp hadj.1.2 hxH hxK
  let b : Fin C := κ (H, i)
  let U : Finset (Fin R) := Finset.univ \ (A ∪ B)
  have hbT : b ∉ T := by
    intro hb
    apply (hS i).2 ⟨A, hA⟩
    · exact Finset.subset_union_left
    · simpa [b, κ, A] using hb
  let Kidx : Finset (Fin (C + 1)) := (Finset.univ.erase i).erase j
  let Q : Finset (Fin R) := Kidx.biUnion S
  have hKdata := index_pair_data i j hij
  have hKcard : Kidx.card = C - 1 := hKdata.1
  have hKne : Kidx.Nonempty := by
    rw [← Finset.card_pos, hKcard]
    omega
  have hQcard : Q.card ≤ (C - 1) * s := by
    dsimp [Q]
    rw [Finset.card_biUnion]
    · calc
        ∑ k ∈ Kidx, (S k).card ≤ ∑ _k ∈ Kidx, s :=
          Finset.sum_le_sum fun k _ => (hS k).1
        _ = (C - 1) * s := by simp [hKcard]
    · intro k _ l _ hkl
      exact hdisj k l hkl
  have hQsubU : Q ⊆ U := by
    intro x hx
    obtain ⟨k, hkK, hxk⟩ := Finset.mem_biUnion.mp hx
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hkK).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hkK).1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_union, not_or]
    constructor
    · intro hxA
      rcases Finset.mem_union.mp hxA with hxSi | hxH
      · exact Finset.disjoint_left.mp (hdisj k i hki) hxk hxSi
      · have hxP : x ∈ P := hSP k hxk
        exact Finset.disjoint_left.mp hZdisjP (hHZ hxH) hxP
    · intro hxB
      rcases Finset.mem_union.mp hxB with hxSj | hxK
      · exact Finset.disjoint_left.mp (hdisj k j hkj) hxk hxSj
      · have hxP : x ∈ P := hSP k hxk
        exact Finset.disjoint_left.mp hZdisjP (hKZ hxK) hxP
  let Z0 : Finset (Fin R) := Z \ (H.val ∪ K.val)
  have hHKdisj : Disjoint H.val K.val := hadj.1.2
  have hHKcard : (H.val ∪ K.val).card = 2 * h := by
    rw [Finset.card_union_of_disjoint hHKdisj, H.property.1, K.property.1]
    omega
  have hHKsub : H.val ∪ K.val ⊆ Z := Finset.union_subset hHZ hKZ
  have hZ0card : Z0.card = Z.card - 2 * h := by
    dsimp [Z0]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hHKsub, hHKcard]
  have hZ0bound : Z0.card ≤ C := by omega
  have hUsub : U ⊆ Q ∪ Z0 := by
    intro x hx
    by_cases hxP : x ∈ P
    · rw [hP] at hxP
      obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hxP
      have hxi : x ∉ S i := by
        intro hxi
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ (Finset.mem_union_left _ hxi))
      have hxj : x ∉ S j := by
        intro hxj
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ (Finset.mem_union_left _ hxj))
      have hki : k ≠ i := by rintro rfl; exact hxi hxk
      have hkj : k ≠ j := by rintro rfl; exact hxj hxk
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨k, by simp [Kidx, hki, hkj], hxk⟩
    · apply Finset.mem_union_right
      have hxZ : x ∈ Z := by simp [hZ, hxP]
      apply Finset.mem_sdiff.mpr
      refine ⟨hxZ, ?_⟩
      simp only [Finset.mem_union, not_or]
      constructor
      · intro hxH
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ (Finset.mem_union_right _ hxH))
      · intro hxK
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ (Finset.mem_union_right _ hxK))
  have hcard : U.card ≤ (C - 1) * s + C := by
    calc
      U.card ≤ (Q ∪ Z0).card := Finset.card_le_card hUsub
      _ ≤ Q.card + Z0.card := Finset.card_union_le _ _
      _ ≤ (C - 1) * s + C := Nat.add_le_add hQcard hZ0bound
  refine ⟨b, U, hbT, hcard, ?_⟩
  intro X hX
  simp only [Finset.mem_insert, not_or]
  constructor
  · intro hXb
    have hnae : BooleanNAE A B X := booleanNAE_sdiff _ _ _ hABdisj hX
    apply hf ⟨A, hA⟩ ⟨B, hB⟩ X hnae
    constructor
    · change κ (H, i) = κ (K, j)
      exact hcol
    · change κ (K, j) = f X
      calc
        κ (K, j) = κ (H, i) := hcol.symm
        _ = b := rfl
        _ = f X := hXb.symm
  · obtain ⟨k, hk⟩ := hKne
    have hkU : S k ⊆ U := by
      intro x hxk
      apply hQsubU
      exact Finset.mem_biUnion.mpr ⟨k, hk, hxk⟩
    exact (hS k).2 X (hkU.trans hX)

theorem solution (C s R : ℕ) (hC : 2 ≤ C) (hs : 1 ≤ s) (hR : 1 ≤ R)
    (W : Finset (Finset (Fin R))) (hcore : Core C s R ⊆ W) (f : W → Fin C)
    (hf : Admissible f) :
    (∃ S : Finset (Fin R), S.Nonempty ∧ S.card ≤ C ∧ AvoidsNumber f S 1) ∧
    (∀ (T : Finset (Fin C)) (S : Fin (C + 1) → Finset (Fin R)),
      T.card ≤ C - 1 → (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, (S i).card ≤ s ∧ Avoids f (S i) T) →
      ∃ (b : Fin C) (U : Finset (Fin R)), b ∉ T ∧ U.card ≤ (C - 1) * s + C ∧
        Avoids f U (insert b T)) := by
  classical
  refine ⟨avoiding_first C s R hC hR W hcore f hf, ?_⟩
  intro T S hT hdisj hS
  let P : Finset (Fin R) := Finset.univ.biUnion S
  let Z : Finset (Fin R) := Finset.univ \ P
  have hPcard : P.card ≤ (C + 1) * s := by
    calc
      P.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin (C + 1))), (S i).card := by
        exact Finset.card_biUnion_le
      _ = ∑ i : Fin (C + 1), (S i).card := by simp
      _ ≤ ∑ _i : Fin (C + 1), s := Finset.sum_le_sum fun i _ => (hS i).1
      _ = (C + 1) * s := by simp
  by_cases hZsmall : Z.card ≤ C
  · exact avoiding_second_small C s R hC W hcore f hf T S hT hdisj hS
      P Z rfl rfl hPcard hZsmall
  · exact avoiding_second_large C s R hC W hcore f hf T S hT hdisj hS
      P Z rfl rfl hPcard (Nat.lt_of_not_ge hZsmall)
