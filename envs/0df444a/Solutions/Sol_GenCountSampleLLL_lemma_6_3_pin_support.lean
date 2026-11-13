-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_3_pin_support
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:16:27.298107+00:00
-- url     : https://prove2.me/submissions/1cb4577b-5b32-462a-882c-475fb58e126a

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators
open GenCountSampleLLL

private theorem pinned_sigT (I : Inst) (D T : Finset (Fin I.m)) (z : I.Assign)
    (hz : z = I.restr (I.UT D T) z) (ω : I.ExpSpace) :
    I.sigT D T (I.pin (T,z) ω) = z := by
  calc
    _ = I.restr (I.UT D T) z := by
      apply funext
      intro v
      unfold Inst.sigT Inst.restr
      by_cases hv : v ∈ I.UT D T
      · simp only [hv]
        by_cases ht : ∃ t, t ∈ T ∧ v ∈ I.vbl t
        · simp only [ht, ↓reduceDIte, Inst.pin]
          simp [(Classical.choose_spec ht).1]
        · simp [ht, Inst.pin]
      · simp [hv]
    _ = z := hz.symm

private theorem pinned_entry_present (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) (ω : I.ExpSpace) :
    (T,z) ∈ I.Le D a (T,z) ω := by
  have hzE : z ∈ I.ET D a T := (Finset.mem_filter.mp hz).1
  have hzR : z = I.restr (I.UT D T) z := (Finset.mem_filter.mp hz).2
  have hs : I.sigT D T (I.pin (T,z) ω) = z := pinned_sigT I D T z hzR ω
  unfold Inst.Le Inst.Llist
  apply Finset.mem_image.mpr
  refine ⟨T, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hT, ?_⟩
    rw [hs]
    exact (Finset.mem_filter.mp hzE).2
  · simp [hs]

private theorem entry_mem_iff (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign) (ω : I.ExpSpace) :
    (T,z) ∈ I.Llist D a ω ↔
      T ∈ I.twoTrees D a ∧ I.inET D a T (I.sigT D T ω) ∧ I.sigT D T ω = z := by
  unfold Inst.Llist
  constructor
  · intro he
    obtain ⟨S, hS, hpair⟩ := Finset.mem_image.mp he
    have hST : S = T := congrArg Prod.fst hpair
    subst S
    refine ⟨(Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2, ?_⟩
    exact congrArg Prod.snd hpair
  · rintro ⟨hT, hET, heq⟩
    apply Finset.mem_image.mpr
    exact ⟨T, Finset.mem_filter.mpr ⟨hT, hET⟩, by simp [heq]⟩

private theorem valid_entry_mem_iff_sigT (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign) (ω : I.ExpSpace)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (T,z) ∈ I.Llist D a ω ↔ I.sigT D T ω = z := by
  rw [entry_mem_iff]
  constructor
  · exact fun h => h.2.2
  · intro heq
    refine ⟨hT, ?_, heq⟩
    rw [heq]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2

private theorem nuU_positive (I : Inst) (U : Finset (Fin I.n)) (z : I.Assign) :
    0 < I.nuU U z := by
  unfold Inst.nuU
  apply Finset.prod_pos
  intro v hv
  exact ENNReal.toReal_pos (I.ν_pos v (z v)) ((I.ν v).apply_ne_top (z v))

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∀ ω : I.ExpSpace, ((T,z) ∈ I.Llist D a ω ↔ I.sigT D T ω = z) ∧
      (T,z) ∈ I.Le D a (T,z) ω) ∧ 0 < I.nuU (I.UT D T) z := by
  exact ⟨fun ω => ⟨valid_entry_mem_iff_sigT I D a T z ω hT hz,
    pinned_entry_present I D a T z hT hz ω⟩, nuU_positive I _ z⟩

