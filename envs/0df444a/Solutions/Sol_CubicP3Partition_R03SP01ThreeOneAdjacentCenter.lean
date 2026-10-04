-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneAdjacentCenter
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T12:41:29.783617+00:00
-- url     : https://prove2.me/submissions/ec5aa249-31c8-4f27-a382-0af096645a22

import Definitions.Def_r03_defs_70d95c7a2a_r03_sp01_three_one_adjacent_center_candidate_v1
import Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
import Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsIndexEquivMod1

universe u
open CubicP3Partition
open SimpleGraph

namespace CubicP3Partition

theorem R03SP01ThreeOneAdjacentCenter
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (kA kB kC : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (eC : Fin (1 + kC * 3) ≃ C)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + kB * 3), Nat.mod_lt _ (by omega)⟩))))
    (cycleC : ∀ i : Fin (1 + kC * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (1 + kC * 3), Nat.mod_lt _ (by omega)⟩))))
    (hkA : 0 < kA)
    (hcrossAB : G.Adj (Sum.inl (eA ⟨0, by omega⟩))
      (Sum.inr (Sum.inl (eB ⟨0, by omega⟩))))
    (hcrossAC : G.Adj (Sum.inl (eA ⟨1, by omega⟩))
      (Sum.inr (Sum.inr (eC ⟨0, by omega⟩)))) :
    Nonempty (P3Factor G) := by
  classical
  let lowToHigh :
      (Fin (1 + kB * 3) ⊕ (Fin (1 + kA * 3) ⊕ Fin (1 + kC * 3))) ≃
        (A ⊕ (B ⊕ C)) :=
    { toFun := fun x => match x with
        | Sum.inl b => Sum.inr (Sum.inl (eB b))
        | Sum.inr (Sum.inl a) => Sum.inl (eA a)
        | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr (eC c))
      invFun := fun x => match x with
        | Sum.inl a => Sum.inr (Sum.inl (eA.symm a))
        | Sum.inr (Sum.inl b) => Sum.inl (eB.symm b)
        | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr (eC.symm c))
      left_inv := by intro x; rcases x with x | (x | x) <;> simp
      right_inv := by intro x; rcases x with x | (x | x) <;> simp }
  let G' : SimpleGraph
      (Fin (1 + kB * 3) ⊕ (Fin (1 + kA * 3) ⊕ Fin (1 + kC * 3))) :=
    G.comap lowToHigh

  obtain ⟨e0, hleft, hmid, h0, h1, h2, h3⟩ :=
    R03SP01ThreeOneArbitraryPortsIndexEquivMod1 kA 1 (by omega) (by omega) (by norm_num)
  have hfirst : 0 * 3 = 1 - 1 := by omega
  have hmiddle : (kA - 1) * 3 = (1 + 3 * kA) - 1 - 3 := by omega
  have htarget : 1 + 3 * kA = 1 + kA * 3 := by omega
  let eIndex : Fin (0 * 3) ⊕ (Fin ((kA - 1) * 3) ⊕ Fin 4) ≃
      Fin (1 + kA * 3) :=
    (Equiv.sumCongr (finCongr hfirst)
      (Equiv.sumCongr (finCongr hmiddle) (Equiv.refl (Fin 4)))).trans
        (e0.trans (finCongr htarget))
  have eIndex_mid (i : Fin (kA - 1)) (j : Fin 3) :
      eIndex (Sum.inr (Sum.inl (finProdFinEquiv (i, j)))) =
        ⟨3 + 3 * i.val + j.val, by
          have hi := i.isLt
          omega⟩ := by
    change (finCongr htarget)
      (e0 (Sum.inr (Sum.inl
        ((finCongr hmiddle) (finProdFinEquiv (i, j)))))) = _
    rw [hmid]
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have eIndex_0 : eIndex (Sum.inr (Sum.inr (0 : Fin 4))) = ⟨0, by omega⟩ := by
    simpa [eIndex] using h0
  have eIndex_1 : eIndex (Sum.inr (Sum.inr (1 : Fin 4))) = ⟨1, by omega⟩ := by
    change (finCongr htarget) (e0 (Sum.inr (Sum.inr (1 : Fin 4)))) = _
    rw [h1]
    apply Fin.ext
    rfl
  have eIndex_2 : eIndex (Sum.inr (Sum.inr (2 : Fin 4))) = ⟨2, by omega⟩ := by
    change (finCongr htarget) (e0 (Sum.inr (Sum.inr (2 : Fin 4)))) = _
    rw [h2]
    apply Fin.ext
    rfl
  have eIndex_3 : eIndex (Sum.inr (Sum.inr (3 : Fin 4))) = ⟨kA * 3, by omega⟩ := by
    change (finCongr htarget) (e0 (Sum.inr (Sum.inr (3 : Fin 4)))) = _
    rw [h3]
    apply Fin.ext
    simp
    omega
  have shift_res (k : Nat) (i : Fin k) (j : Fin 3) :
      (finSumFinEquiv.trans (finAddFlip (m := k * 3) (n := 1)))
          (Sum.inl (finProdFinEquiv (i, j))) =
        ⟨1 + 3 * i.val + j.val, by omega⟩ := by
    rw [show (finSumFinEquiv.trans (finAddFlip (m := k * 3) (n := 1)))
        (Sum.inl (finProdFinEquiv (i, j))) =
        Fin.natAdd 1 (finProdFinEquiv (i, j)) by
      simp [finSumFinEquiv, finAddFlip]]
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have shift_exc (k : Nat) :
      (finSumFinEquiv.trans (finAddFlip (m := k * 3) (n := 1)))
          (Sum.inr (0 : Fin 1)) = (0 : Fin (1 + k * 3)) := by
    apply Fin.ext
    simp [finSumFinEquiv, finAddFlip]
  have cycleA_step (n : Nat) (hn : n + 1 < 1 + kA * 3) :
      G'.Adj (Sum.inr (Sum.inl ⟨n, by omega⟩))
        (Sum.inr (Sum.inl ⟨n + 1, by omega⟩)) := by
    have h := cycleA ⟨n, by omega⟩
    have hs : (⟨(n + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (1 + kA * 3)) = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hn
    rw [hs] at h
    simpa [G', lowToHigh] using h
  have cycleB_step (n : Nat) (hn : n + 1 < 1 + kB * 3) :
      G'.Adj (Sum.inl ⟨n, by omega⟩)
        (Sum.inl ⟨n + 1, by omega⟩) := by
    have h := cycleB ⟨n, by omega⟩
    have hs : (⟨(n + 1) % (1 + kB * 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (1 + kB * 3)) = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hn
    rw [hs] at h
    simpa [G', lowToHigh] using h
  have cycleC_step (n : Nat) (hn : n + 1 < 1 + kC * 3) :
      G'.Adj (Sum.inr (Sum.inr ⟨n, by omega⟩))
        (Sum.inr (Sum.inr ⟨n + 1, by omega⟩)) := by
    have h := cycleC ⟨n, by omega⟩
    have hs : (⟨(n + 1) % (1 + kC * 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (1 + kC * 3)) = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hn
    rw [hs] at h
    simpa [G', lowToHigh] using h

  let bres (i : Fin kB) (j : Fin 3) :
      Fin (1 + kB * 3) ⊕ (Fin (1 + kA * 3) ⊕ Fin (1 + kC * 3)) :=
    Sum.inl ((finSumFinEquiv.trans (finAddFlip (m := kB * 3) (n := 1)))
      (Sum.inl (finProdFinEquiv (i, j))))
  have hBraw : ∀ i : Fin kB,
      G'.Adj (bres i 0) (bres i 1) ∧ G'.Adj (bres i 1) (bres i 2) := by
    intro i
    constructor
    · simp only [bres]
      rw [shift_res kB i 0, shift_res kB i 1]
      exact cycleB_step (1 + 3 * i.val) (by omega)
    · simp only [bres]
      rw [shift_res kB i 1, shift_res kB i 2]
      exact cycleB_step (1 + 3 * i.val + 1) (by omega)
  have hEmpty : ∀ i : Fin 0,
      G'.Adj
          (Sum.inr (Sum.inl (eIndex (Sum.inl (finProdFinEquiv (i, (0 : Fin 3)))))))
          (Sum.inr (Sum.inl (eIndex (Sum.inl (finProdFinEquiv (i, (1 : Fin 3))))))) ∧
      G'.Adj
          (Sum.inr (Sum.inl (eIndex (Sum.inl (finProdFinEquiv (i, (1 : Fin 3)))))))
          (Sum.inr (Sum.inl (eIndex (Sum.inl (finProdFinEquiv (i, (2 : Fin 3))))))) := by
    intro i
    exact Fin.elim0 i
  let ares (i : Fin (kA - 1)) (j : Fin 3) :
      Fin (1 + kB * 3) ⊕ (Fin (1 + kA * 3) ⊕ Fin (1 + kC * 3)) :=
    Sum.inr (Sum.inl (eIndex
      (Sum.inr (Sum.inl (finProdFinEquiv (i, j))))))
  have hAres : ∀ i : Fin (kA - 1),
      G'.Adj (ares i 0) (ares i 1) ∧ G'.Adj (ares i 1) (ares i 2) := by
    intro i
    constructor
    · simp only [ares]
      rw [eIndex_mid i 0, eIndex_mid i 1]
      exact cycleA_step (3 + 3 * i.val) (by have hi := i.isLt; omega)
    · simp only [ares]
      rw [eIndex_mid i 1, eIndex_mid i 2]
      exact cycleA_step (3 + 3 * i.val + 1) (by have hi := i.isLt; omega)
  let cres (i : Fin kC) (j : Fin 3) :
      Fin (1 + kB * 3) ⊕ (Fin (1 + kA * 3) ⊕ Fin (1 + kC * 3)) :=
    Sum.inr (Sum.inr
      ((finSumFinEquiv.trans (finAddFlip (m := kC * 3) (n := 1)))
        (Sum.inl (finProdFinEquiv (i, j)))))
  have hCraw : ∀ i : Fin kC,
      G'.Adj (cres i 0) (cres i 1) ∧ G'.Adj (cres i 1) (cres i 2) := by
    intro i
    constructor
    · simp only [cres]
      rw [shift_res kC i 0, shift_res kC i 1]
      exact cycleC_step (1 + 3 * i.val) (by omega)
    · simp only [cres]
      rw [shift_res kC i 1, shift_res kC i 2]
      exact cycleC_step (1 + 3 * i.val + 1) (by omega)
  have hLast0 : G'.Adj
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (3 : Fin 4))))))
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (0 : Fin 4)))))) := by
    rw [eIndex_3, eIndex_0]
    have h := cycleA ⟨kA * 3, by omega⟩
    have hs : (⟨(kA * 3 + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (1 + kA * 3)) = 0 := by
      apply Fin.ext
      simpa only [Fin.val_mk, Fin.val_zero, show kA * 3 + 1 = 1 + kA * 3 by omega]
        using Nat.mod_self (1 + kA * 3)
    rw [hs] at h
    simpa [G', lowToHigh] using h
  have h0B0 : G'.Adj
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))
      (Sum.inl ((finSumFinEquiv.trans (finAddFlip (m := kB * 3) (n := 1)))
        (Sum.inr (0 : Fin 1)))) := by
    rw [eIndex_0]
    rw [shift_exc kB]
    simpa [G', lowToHigh] using hcrossAB
  have hC0A1 : G'.Adj
      (Sum.inr (Sum.inr ((finSumFinEquiv.trans (finAddFlip (m := kC * 3) (n := 1)))
        (Sum.inr (0 : Fin 1)))))
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (1 : Fin 4)))))) := by
    rw [eIndex_1]
    rw [shift_exc kC]
    simpa [G', lowToHigh] using hcrossAC.symm
  have hA1A2 : G'.Adj
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))
      (Sum.inr (Sum.inl (eIndex (Sum.inr (Sum.inr (2 : Fin 4)))))) := by
    rw [eIndex_1, eIndex_2]
    have h := cycleA ⟨1, by omega⟩
    have hs : (⟨2 % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩ :
        Fin (1 + kA * 3)) = 2 := by apply Fin.ext; simp
    rw [hs] at h
    have hN4 : 4 ≤ 1 + kA * 3 := by omega
    have hfin1 : (⟨1, by omega⟩ : Fin (1 + kA * 3)) = 1 := by
      apply Fin.ext
      symm
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (by norm_num) hN4)
    have hfin2 : (⟨2, by omega⟩ : Fin (1 + kA * 3)) = 2 := by
      apply Fin.ext
      symm
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (by norm_num) hN4)
    rw [hfin1] at h
    rw [hfin1, hfin2]
    simpa [G', lowToHigh] using h
  obtain ⟨p⟩ := R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
    G' kB kA kC 0 (kA - 1) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) eIndex
    hBraw hEmpty hAres hCraw hLast0 h0B0 hC0A1 hA1A2
  exact ⟨{
    blockCount := p.blockCount
    place := p.place.trans lowToHigh
    edge01 := by intro i; simpa [G', lowToHigh] using p.edge01 i
    edge12 := by intro i; simpa [G', lowToHigh] using p.edge12 i
  }⟩

end CubicP3Partition

theorem solution
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (kA kB kC : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (eC : Fin (1 + kC * 3) ≃ C)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + kB * 3), Nat.mod_lt _ (by omega)⟩))))
    (cycleC : ∀ i : Fin (1 + kC * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (1 + kC * 3), Nat.mod_lt _ (by omega)⟩))))
    (hkA : 0 < kA)
    (hcrossAB : G.Adj (Sum.inl (eA ⟨0, by omega⟩))
      (Sum.inr (Sum.inl (eB ⟨0, by omega⟩))))
    (hcrossAC : G.Adj (Sum.inl (eA ⟨1, by omega⟩))
      (Sum.inr (Sum.inr (eC ⟨0, by omega⟩)))) :
    Nonempty (P3Factor G) := by
  exact CubicP3Partition.R03SP01ThreeOneAdjacentCenter G kA kB kC eA eB eC
    cycleA cycleB cycleC hkA hcrossAB hcrossAC
