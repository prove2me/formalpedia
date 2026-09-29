-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_mem_nPiece
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/76c15e75-c439-52d4-944b-1af063ddda48

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

namespace D2Aux

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem eq_zero_of_mem_piece_of_mem_piece_succ (D : GradedCartierModuleData p B j) (m : Fin 2) (y : D.M)
    (h1 : y ∈ D.piece m) (h2 : y ∈ D.piece (m + 1)) : y = 0 := by
  have hd := Submodule.disjoint_def.1 D.isCompl_piece.disjoint
  fin_cases m
  · exact hd y h1 h2
  · exact hd y h2 h1

theorem lambda_mem_piece_succ (D : GradedCartierModuleData p B j) (m : Fin 2) (n : D.NMod)
    (hn : n ∈ D.nPiece m) : D.lambda n ∈ D.piece (m + 1) := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [lambda_nMk]
  exact Submodule.add_mem _ (D.varpi_mem m a ha) (D.verschiebung_mem m b hb)

theorem smul_mem_nPiece (D : GradedCartierModuleData p B j) (m : Fin 2) (w : WittVector p B) (n : D.NMod)
    (hn : n ∈ D.nPiece m) : w • n ∈ D.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [smul_nMk]
  exact AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.mem_prod.mpr ⟨Submodule.smul_mem _ _ ha, Submodule.smul_mem _ _ hb⟩, rfl⟩

theorem nMap_mem_nPiece {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (m : Fin 2) (n : D.NMod) (hn : n ∈ D.nPiece m) : D.nMap D' f hV hPi n ∈ D'.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [nMap_nMk]
  exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc m a ha, hpc m b hb⟩, rfl⟩

theorem exists_nPiece_add (D : GradedCartierModuleData p B j) (m : Fin 2) (n : D.NMod) :
    ∃ a ∈ D.nPiece m, ∃ b ∈ D.nPiece (m + 1), n = a + b := by
  have hN := CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p j D
  have : n ∈ D.nPiece 0 ⊔ D.nPiece 1 := by rw [hN.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, h⟩ := AddSubgroup.mem_sup.mp this
  fin_cases m
  · exact ⟨a, ha, b, hb, h.symm⟩
  · exact ⟨b, hb, a, ha, by rw [← h, add_comm]⟩

theorem exists_piece_add (D : GradedCartierModuleData p B j) (m : Fin 2) (x : D.M) :
    ∃ a ∈ D.piece m, ∃ b ∈ D.piece (m + 1), x = a + b := by
  have : x ∈ D.piece 0 ⊔ D.piece 1 := by rw [D.isCompl_piece.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, h⟩ := Submodule.mem_sup.mp this
  fin_cases m
  · exact ⟨a, ha, b, hb, h.symm⟩
  · exact ⟨b, hb, a, ha, by rw [← h, add_comm]⟩

end D2Aux

open D2Aux in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    L x ∈ D.nPiece i := by
  classical
  obtain ⟨S, _, jS, φ, hφ, htf, Dl, hDl, f, hf, Ll, hLl, hcomp⟩ := hL.exists_lift
  obtain ⟨γ, hγl, hγ⟩ := hf.2.2.2.2.2
  have hinj := CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree
    p jS htf Dl γ hγl

  have step1 : ∀ k : Fin 2, Ll (γ k) ∈ Dl.nPiece k := by
    intro k
    obtain ⟨a, ha, b, hb, hab⟩ := exists_nPiece_add Dl k (Ll (γ k))
    have hla : Dl.lambda a ∈ Dl.piece (k + 1) := lambda_mem_piece_succ Dl k a ha
    have hlb : Dl.lambda b ∈ Dl.piece (k + 1 + 1) := lambda_mem_piece_succ Dl (k + 1) b hb
    have hF : Dl.lambda (Ll (γ k)) ∈ Dl.piece (k + 1) := by
      rw [hLl.lambda_comp]; exact Dl.frobenius_mem k _ (hγl.1 k)
    have hlb' : Dl.lambda b ∈ Dl.piece (k + 1) := by
      have : Dl.lambda b = Dl.lambda (Ll (γ k)) - Dl.lambda a := by rw [hab, map_add]; abel
      rw [this]; exact Submodule.sub_mem _ hF hla
    have hb0 : Dl.lambda b = 0 := eq_zero_of_mem_piece_of_mem_piece_succ Dl (k + 1) _ hlb' hlb
    have : b = 0 := hinj (by rw [hb0, map_zero])
    rw [hab, this, add_zero]; exact ha

  have step2 : ∀ k : Fin 2, L (f (γ k)) ∈ D.nPiece k := by
    intro k
    rw [hcomp]
    exact nMap_mem_nPiece Dl D f hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 k _ (step1 k)

  obtain ⟨⟨c, y⟩, hxy, -⟩ := hγ.2 x
  simp only at hxy
  obtain ⟨y₀, hy₀, y₁, hy₁, hyy⟩ := exists_piece_add D (i + 1) y

  set A : D.M := WittVector.teichmuller p (c i) • f (γ i) + D.verschiebung y₀ with hA
  set Bp : D.M := WittVector.teichmuller p (c (i + 1)) • f (γ (i + 1)) + D.verschiebung y₁ with hBp
  have e2 : (i + 1 + 1 : Fin 2) = i := by fin_cases i <;> rfl
  have hAi : A ∈ D.piece i := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 i)) ?_
    have := D.verschiebung_mem (i + 1) y₀ hy₀
    rw [e2] at this; exact this
  have hBi : Bp ∈ D.piece (i + 1) := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 (i + 1))) ?_
    have := D.verschiebung_mem (i + 1 + 1) y₁ hy₁
    have e : (i + 1 + 1 + 1 : Fin 2) = i + 1 := by fin_cases i <;> rfl
    rw [e] at this; exact this
  have hsum2 : (∑ k : Fin 2, WittVector.teichmuller p (c k) • f (γ k)) =
      WittVector.teichmuller p (c i) • f (γ i) + WittVector.teichmuller p (c (i + 1)) • f (γ (i + 1)) := by
    rw [Fin.sum_univ_two]
    fin_cases i
    · rfl
    · show _ = WittVector.teichmuller p (c 1) • f (γ 1) + WittVector.teichmuller p (c (1 + 1)) • f (γ (1 + 1))
      have e : ((1 : Fin 2) + 1) = 0 := rfl
      rw [e, add_comm]
  have hxAB : x = A + Bp := by
    rw [hxy, hsum2, hyy, map_add, hA, hBp]; abel
  have hB0 : Bp = 0 := by
    have : Bp = x - A := by rw [hxAB]; abel
    have hBi' : Bp ∈ D.piece i := by rw [this]; exact Submodule.sub_mem _ hx hAi
    exact eq_zero_of_mem_piece_of_mem_piece_succ D i _ hBi' hBi
  rw [hxAB, hB0, add_zero, hA, map_add, hL.isCartierLMap.map_smul, hL.isCartierLMap.map_verschiebung]
  refine AddSubgroup.add_mem _ (smul_mem_nPiece D i _ _ (step2 i)) ?_
  refine AddSubgroup.mem_map.mpr ⟨(D.varpi y₀, 0), AddSubgroup.mem_prod.mpr ⟨?_, Submodule.zero_mem _⟩, rfl⟩
  have := D.varpi_mem (i + 1) y₀ hy₀
  rw [e2] at this; exact this

end S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece (solution)
