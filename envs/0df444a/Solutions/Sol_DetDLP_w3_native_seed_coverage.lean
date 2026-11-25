-- Prove2me | solution 1 for DetDLP.w3_native_seed_coverage
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:30:12.830374+00:00
-- url     : https://prove2.me/submissions/0568a7f4-fb85-4404-bdf2-6f89d9418acd

import Definitions.Def_DetDLP_W3_Driver
import Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
import Theorems.Thm_DetDLP_lemma_3_2_collision_potential

set_option autoImplicit false
open DetDLP

private theorem DetDLP.w3_seed_below {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ)
    (h : (∑ s, f s) / (Fintype.card α : ℝ) ≤ 373/336) : ∃ s, f s < 64/57 := by
  classical
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hle := (div_le_iff₀ hc).mp h
  have hh : ∑ s, f s < ∑ _s : α, (64/57 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; linarith
  obtain ⟨s,_,hs⟩ := Finset.exists_lt_of_sum_lt hh
  exact ⟨s,hs⟩

private theorem DetDLP.w3_seed_mu_pos {p n m g : ℕ} (hp : 0 < p) (hn : 0 < n) (hm : 0 < m) :
    0 < (qBlk p n (hashThreshold p n m g))^m := by
  have hstar : 0 < qStar m g := lt_of_lt_of_le (by omega : 0 < 4096*m) (le_max_left ..)
  unfold qBlk hashThreshold
  positivity

private theorem DetDLP.w3_cover_from_pair {G : Type} [AddCommGroup G] {m : ℕ}
    (B : IndexedFactorBase G m) (g : G) (A D : Fin m → G)
    (hAD : ∀ i, A i ∈ B.blocks i ∧ D i ∈ B.blocks i) (hg : (∑ i, (A i + D i)) = g) :
    ∃ X : B.BlockTuple, B.tupleVal X = g := by
  classical
  choose a ha using fun i => List.mem_iff_get.mp (hAD i).1
  choose d hd using fun i => List.mem_iff_get.mp (hAD i).2
  refine ⟨fun i j => if j = 0 then a i else d i,?_⟩
  change (∑ i, ((B.blocks i).get (a i) + (B.blocks i).get (d i))) = g
  simpa only [ha,hd] using hg

theorem solution :
    (∀ (p : ℕ) [Fact p.Prime], let M := p-1; let m := blockCount (bitLen p)
      w3_large p M → ∃ (s : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
        (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) s i) ∧
        Function.Surjective (w3_fpFB B).tupleVal) ∧
    (∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; let M := Fintype.card E.toAffine.Point; let m := blockCount (bitLen p)
      w3_large p M → ∃ (s : ECSeed p m) (B : Fin m → List E.toAffine.Point),
        (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) s i) ∧
        Function.Surjective (IndexedFactorBase.mk B).tupleVal) := by
  classical
  constructor
  · intro p hp M m hg
    obtain ⟨hp67,hM,hbig⟩ := hg
    let T := hashThreshold p M m M; let μ := (qBlk p M T)^m
    have hm : 2 ≤ m := le_max_left ..
    letI : NeZero (p-1) := ⟨by omega⟩
    have hμ : 0 < μ := w3_seed_mu_pos (by omega) (by omega) (by omega)
    have hmean := lemma_3_2_collision_potential.2 p m hm hM (by omega)
    obtain ⟨s,hs⟩ := w3_seed_below (fun s : FpSeed p m => collisionPotentialMul μ (fpFactorBlock T s)) hmean
    let B := fun i => (fpFactorBlock T s i).toList
    refine ⟨s,B,fun i => ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩,?_⟩
    intro g
    obtain ⟨a,d,hm',he⟩ := (dense_covering_and_2m_decomp.2 μ _ hμ hs).2 g.toMul
    apply w3_cover_from_pair (w3_fpFB B) g (fun i => Additive.ofMul (a i)) (fun i => Additive.ofMul (d i)) _ he
    intro i
    exact ⟨List.mem_map.mpr ⟨_,Finset.mem_toList.mpr (hm' i).1,rfl⟩,
      List.mem_map.mpr ⟨_,Finset.mem_toList.mpr (hm' i).2,rfl⟩⟩
  · intro p hp E hE
    letI := ecPointFintype E
    let M := Fintype.card E.toAffine.Point; let m := blockCount (bitLen p)
    dsimp only
    intro hg
    change w3_large p M at hg
    obtain ⟨hp67,hM,hbig⟩ := hg
    let T := hashThreshold p (M-1) m M; let μ := (qBlk p (M-1) T)^m
    have hm : 2 ≤ m := le_max_left ..
    letI : NeZero (p-1) := ⟨by omega⟩
    have hμ : 0 < μ := w3_seed_mu_pos (by omega) (by omega) (by omega)
    have hmean := lemma_3_2_collision_potential.1 p m (by omega) hm E hM hbig
    obtain ⟨s,hs⟩ := w3_seed_below (fun s : ECSeed p m => collisionPotentialAdd μ (ecFactorBlock E T s)) hmean
    let B := fun i => (ecFactorBlock E T s i).toList
    refine ⟨s,B,fun i => ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩,?_⟩
    intro g
    obtain ⟨a,d,hm',he⟩ := (dense_covering_and_2m_decomp.1 μ _ hμ hs).2 g
    exact w3_cover_from_pair ⟨B⟩ g a d (fun i => ⟨Finset.mem_toList.mpr (hm' i).1,Finset.mem_toList.mpr (hm' i).2⟩) he
