-- Prove2me | solution 1 for GenCountSampleLLL.insertion_tree_forward_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:06:00.113802+00:00
-- url     : https://prove2.me/submissions/59341ce7-1767-4280-945c-ae7f2d09c851

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

private theorem DT_scope_disjoint_UT (I : Inst) (D T : Finset (Fin I.m))
    (b : Fin I.m) (hb : b ∈ I.DT D T) : Disjoint (I.vbl b) (I.UT D T) := by
  apply Finset.disjoint_left.mpr
  intro v hvb hvU
  have hbd : b ∈ D := (Finset.mem_sdiff.mp hb).1
  have hnot : b ∉ I.N2Dc D T := (Finset.mem_sdiff.mp hb).2
  obtain ⟨c, hcN, hvc⟩ := Finset.mem_biUnion.mp hvU
  have hc : c ∈ T ∨ (c ∈ D ∧ ∃ t ∈ T, I.G.Adj t c) := by
    simpa [Inst.NDc] using hcN
  have hdist (t : Fin I.m) (ht : t ∈ T) (hadj : I.adj2D D t b) : False := by
    apply hnot
    unfold Inst.N2Dc
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbd, ⟨t,ht,hadj⟩⟩)
  rcases hc with hcT | ⟨hcD,t,ht,htc⟩
  · by_cases hbc : b = c
    · subst b
      exact hnot (Finset.mem_union_left _ hcT)
    · have hadj : I.G.Adj c b := by
        change c ≠ b ∧ (I.vbl c ∩ I.vbl b).Nonempty
        exact ⟨Ne.symm hbc, ⟨v, Finset.mem_inter.mpr ⟨hvc,hvb⟩⟩⟩
      exact hdist c hcT (Or.inl hadj)
  · by_cases hbc : b = c
    · subst b
      exact hdist t ht (Or.inl htc)
    · have hcb : I.G.Adj c b := by
        change c ≠ b ∧ (I.vbl c ∩ I.vbl b).Nonempty
        exact ⟨Ne.symm hbc, ⟨v, Finset.mem_inter.mpr ⟨hvc,hvb⟩⟩⟩
      exact hdist t ht (Or.inr ⟨c,hcD,htc,hcb⟩)

private theorem DT_good_preserved_by_resampling (I : Inst) (D T : Finset (Fin I.m))
    (σ τ : I.Assign) (hσ : σ ∈ I.Good (I.DT D T)) :
    I.merge (I.UT D T) τ σ ∈ I.Good (I.DT D T) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro b hb
  have hgood := (Finset.mem_filter.mp hσ).2 b hb
  have hdis := DT_scope_disjoint_UT I D T b hb
  have heq : (fun v : {v // v ∈ I.vbl b} => (I.merge (I.UT D T) τ σ) v.1) =
      (fun v : {v // v ∈ I.vbl b} => σ v.1) := by
    funext v
    have hv : v.1 ∉ I.UT D T := fun hh => (Finset.disjoint_left.mp hdis v.2 hh)
    simp [Inst.merge, hv]
  unfold Inst.bad at *
  rwa [heq]

private theorem bad_restr_iff (I : Inst) (U : Finset (Fin I.n))
    (b : Fin I.m) (σ : I.Assign) (hsub : I.vbl b ⊆ U) :
    I.bad b (I.restr U σ) ↔ I.bad b σ := by
  have heq : (fun v : {v // v ∈ I.vbl b} => I.restr U σ v.1) =
      (fun v : {v // v ∈ I.vbl b} => σ v.1) := by
    funext v
    simp [Inst.restr, hsub v.2]
  unfold Inst.bad
  rw [heq]

private theorem tree_restr_is_label (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (σ : I.Assign) (hσ : σ ∈ I.ET D a T) :
    I.restr (I.UT D T) σ ∈ I.labelsE D a T := by
  have hlocal : ∀ b ∈ T ∪ I.F1 D a T, I.vbl b ⊆ I.UT D T := by
    intro b hb v hv
    have hbN : b ∈ I.NDc D T := by
      rcases Finset.mem_union.mp hb with hbT | hbF
      · exact Finset.mem_union_left _ hbT
      · have hF := Finset.mem_filter.mp hbF
        have hbD : b ∈ D := (Finset.mem_sdiff.mp hF.1).1
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbD,hF.2⟩)
    exact Finset.mem_biUnion.mpr ⟨b,hbN,hv⟩
  have hET := (Finset.mem_filter.mp hσ).2
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · intro b hb
      exact (bad_restr_iff I _ b σ (hlocal b (Finset.mem_union_left _ hb))).mpr (hET.1 b hb)
    · intro b hb
      exact fun hh => hET.2 b hb ((bad_restr_iff I _ b σ (hlocal b (Finset.mem_union_right _ hb))).mp hh)
  · funext v
    by_cases hv : v ∈ I.UT D T <;> simp [Inst.restr, hv]

private theorem tree_resample_layer_valid (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a)
    (σ τ : I.Assign) (hσ : σ ∈ I.Estar D a T) :
    (⟨[], Inst.Base.lay T (I.restr (I.UT D T) σ) 0 (I.merge (I.UT D T) τ σ)⟩ : I.St) ∈
      I.states D.card D a := by
  have hz := tree_restr_is_label I D a T σ (Finset.mem_inter.mp hσ).1
  have hgood := DT_good_preserved_by_resampling I D T σ τ (Finset.mem_inter.mp hσ).2
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  rw [hk, Inst.states]
  apply Finset.mem_union.mpr; left
  apply Finset.mem_union.mpr; right
  apply Finset.mem_biUnion.mpr
  refine ⟨T,hT,Finset.mem_biUnion.mpr ⟨_,hz,?_⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _),?_⟩
  apply Finset.mem_image.mpr
  refine ⟨_, ?_, rfl⟩
  simpa [Inst.DTi] using hgood

private theorem nuA_nonnegative (I : Inst) (σ : I.Assign) : 0 ≤ I.nuA σ := by
  unfold Inst.nuA
  exact Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

private theorem nuA_sum_one (I : Inst) : ∑ σ : I.Assign, I.nuA σ = 1 := by
  have hσ (σ : I.Assign) : I.nuA σ = (I.prodLaw σ).toReal := by
    simp [Inst.nuA, Inst.prodLaw, piLaw, PMF.ofFintype_apply, ENNReal.toReal_prod]
  simp_rw [hσ]
  rw [← ENNReal.toReal_sum (by intro σ h; exact I.prodLaw.apply_ne_top σ)]
  have htotal := I.prodLaw.tsum_coe
  rw [tsum_fintype] at htotal
  rw [htotal]
  simp

private theorem dirac_sum_state (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (s : I.St) (hs : s ∈ I.states D.card D a) :
    (∑ Y : I.S D a, I.dirac s Y.1) = 1 := by
  let s' : I.S D a := ⟨s,hs⟩
  have heq (Y : I.S D a) : (Y.1 = s) ↔ Y = s' := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [Inst.dirac, heq]
  simp

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a)
    (σ : I.Assign) (hσ : σ ∈ I.Estar D a T) :
    (∀ Y : I.S D a, 0 ≤ I.baseRule D a (Inst.Base.tree T σ) Rule.fwd Y.1) ∧
      (∑ Y : I.S D a, I.baseRule D a (Inst.Base.tree T σ) Rule.fwd Y.1) = 1 := by
  constructor
  · intro Y
    simp only [Inst.baseRule]
    apply Finset.sum_nonneg
    intro τ hτ
    apply mul_nonneg (nuA_nonnegative I τ)
    simp [Inst.dirac]
    split_ifs <;> norm_num
  · simp only [Inst.baseRule]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hdir (τ : I.Assign) :
        (∑ Y : I.S D a, I.dirac
          ⟨[], Inst.Base.lay T (I.restr (I.UT D T) σ) 0 (I.merge (I.UT D T) τ σ)⟩ Y.1) = 1 :=
      dirac_sum_state I D a _ (tree_resample_layer_valid I D a ha T hT σ τ hσ)
    simp_rw [hdir, mul_one]
    exact nuA_sum_one I

