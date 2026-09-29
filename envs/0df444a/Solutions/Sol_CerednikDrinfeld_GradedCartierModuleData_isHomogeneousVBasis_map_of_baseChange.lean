-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.isHomogeneousVBasis_map_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/187ef6d9-2a14-5da6-8445-37c19389682c

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange

set_option autoImplicit false

noncomputable section

namespace P2mVbt

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {jR : Zp2 p →+* R}
  (E : GradedCartierModuleData p R jR)

theorem fin2_add_two (i : Fin 2) : i + 1 + 1 = i := by
  fin_cases i <;> rfl

theorem sum_two (i : Fin 2) (t : Fin 2 → E.M) : (∑ k : Fin 2, t k) = t i + t (i + 1) := by
  fin_cases i
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, add_comm]

theorem sum_single (i : Fin 2) (a : R) (δ : Fin 2 → E.M) :
    (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i a : Fin 2 → R) k) • δ k) =
      WittVector.teichmuller p a • δ i := by
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem mem_other_eq_zero (i : Fin 2) {x : E.M} (h1 : x ∈ E.piece i) (h2 : x ∈ E.piece (i + 1)) :
    x = 0 := by
  have d := Submodule.disjoint_def.1 E.isCompl_piece.disjoint
  fin_cases i
  · exact d x h1 h2
  · exact d x (by simpa using h2) h1

theorem exists_piece_decomp (i : Fin 2) (y : E.M) :
    ∃ u u' : E.M, u ∈ E.piece i ∧ u' ∈ E.piece (i + 1) ∧ u + u' = y := by
  have c := Submodule.codisjoint_iff_exists_add_eq.1 E.isCompl_piece.codisjoint y
  fin_cases i
  · simpa using c
  · obtain ⟨u, u', hu, hu', e⟩ := c
    exact ⟨u', u, hu', by simpa using hu, by rw [add_comm]; exact e⟩

theorem diag (γ δ : Fin 2 → E.M) (hγ : ∀ i, γ i ∈ E.piece i) (hδ : E.IsHomogeneousVBasis δ)
    (i : Fin 2) :
    ∃ (a : R) (z : E.M), γ i = WittVector.teichmuller p a • δ i + E.verschiebung z := by
  obtain ⟨⟨c, y⟩, h, -⟩ := hδ.2 (γ i)
  change γ i = (∑ k : Fin 2, WittVector.teichmuller p (c k) • δ k) + E.verschiebung y at h
  obtain ⟨u, u', hu, hu', hy⟩ := exists_piece_decomp E i y
  rw [sum_two E i] at h
  have hA : γ i - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' ∈ E.piece i := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hγ i) (Submodule.smul_mem _ _ (hδ.1 i))) ?_
    have := E.verschiebung_mem (i + 1) u' hu'
    rwa [fin2_add_two] at this
  have hB : WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u ∈ E.piece (i + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hδ.1 (i + 1))) (E.verschiebung_mem i u hu)
  have hAB : γ i - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' =
      WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u := by
    rw [h, ← hy, map_add]; abel
  have hB0 : WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u = 0 :=
    mem_other_eq_zero E i (hAB ▸ hA) hB
  have z1 : (0 : E.M) = (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single (i + 1) (c (i + 1)) : Fin 2 → R) k) • δ k) +
      E.verschiebung u := by
    rw [sum_single E]; exact hB0.symm
  have z2 : (0 : E.M) = (∑ k : Fin 2, WittVector.teichmuller p ((0 : Fin 2 → R) k) • δ k) +
      E.verschiebung 0 := by simp
  have hu0 := (hδ.2 0).unique (y₁ := ((Pi.single (i + 1) (c (i + 1)) : Fin 2 → R), u)) (y₂ := (0, 0)) z1 z2
  have hc : c (i + 1) = 0 := by
    have := congrFun (congrArg Prod.fst hu0) (i + 1)
    simpa using this
  refine ⟨c i, y, ?_⟩
  rw [h, hc]; simp

theorem unit_of_diag (γ δ : Fin 2 → E.M) (hδ : E.IsHomogeneousVBasis δ) (i : Fin 2) (a b : R)
    (z t : E.M) (h1 : γ i = WittVector.teichmuller p a • δ i + E.verschiebung z)
    (h2 : δ i = WittVector.teichmuller p b • γ i + E.verschiebung t) : b * a = 1 := by
  have e : WittVector.teichmuller p b • γ i + E.verschiebung t =
      WittVector.teichmuller p (b * a) • δ i +
        E.verschiebung (WittVector.frobenius (WittVector.teichmuller p b) • z + t) := by
    rw [h1, smul_add, smul_smul, ← map_mul, E.smul_verschiebung, map_add, add_assoc]
  have z1 : δ i = (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i (b * a) : Fin 2 → R) k) • δ k) +
      E.verschiebung (WittVector.frobenius (WittVector.teichmuller p b) • z + t) := by
    rw [sum_single E]; exact h2.trans e
  have z2 : δ i = (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i (1 : R) : Fin 2 → R) k) • δ k) +
      E.verschiebung 0 := by
    rw [sum_single E]; simp
  have := congrFun (congrArg Prod.fst ((hδ.2 _).unique (y₁ := ((Pi.single i (b * a) : Fin 2 → R), _))
    (y₂ := ((Pi.single i (1 : R) : Fin 2 → R), (0 : E.M))) z1 z2)) i
  simpa using this

theorem recombine (c v : Fin 2 → R) (η w : Fin 2 → E.M) (y : E.M) :
    (∑ k : Fin 2, WittVector.teichmuller p (c k) •
        (WittVector.teichmuller p (v k) • η k + E.verschiebung (w k))) + E.verschiebung y =
      (∑ k : Fin 2, WittVector.teichmuller p (c k * v k) • η k) +
        E.verschiebung (y + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (c k)) • w k) := by
  simp only [Fin.sum_univ_two, smul_add, smul_smul, map_mul, E.smul_verschiebung, map_add]
  abel

theorem expand_exists {ε η : Fin 2 → E.M} (hε : E.IsHomogeneousVBasis ε) {v : Fin 2 → R}
    {w : Fin 2 → E.M} (K' : ∀ k, ε k = WittVector.teichmuller p (v k) • η k + E.verschiebung (w k))
    (x : E.M) :
    ∃ (c : Fin 2 → R) (y : E.M), x = (∑ k : Fin 2, WittVector.teichmuller p (c k) • η k) +
      E.verschiebung y := by
  obtain ⟨⟨c, y⟩, h, -⟩ := hε.2 x
  change x = (∑ k : Fin 2, WittVector.teichmuller p (c k) • ε k) + E.verschiebung y at h
  refine ⟨fun k => c k * v k, y + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (c k)) • w k, ?_⟩
  rw [h, show (∑ k : Fin 2, WittVector.teichmuller p (c k) • ε k) =
      ∑ k : Fin 2, WittVector.teichmuller p (c k) •
        (WittVector.teichmuller p (v k) • η k + E.verschiebung (w k)) from
    Finset.sum_congr rfl (fun k _ => by rw [K' k])]
  exact recombine E c v η w y

theorem expand_unique {ε η : Fin 2 → E.M} (hε : E.IsHomogeneousVBasis ε) {u v : Fin 2 → R}
    {w : Fin 2 → E.M} (K : ∀ k, η k = WittVector.teichmuller p (u k) • ε k + E.verschiebung (w k))
    (hvu : ∀ k, v k * u k = 1) (c : Fin 2 → R) (y : E.M) (c' : Fin 2 → R) (y' : E.M)
    (h : (∑ k : Fin 2, WittVector.teichmuller p (c k) • η k) + E.verschiebung y =
      (∑ k : Fin 2, WittVector.teichmuller p (c' k) • η k) + E.verschiebung y') :
    c = c' ∧ y = y' := by
  have H : ∀ (d : Fin 2 → R) (s : E.M),
      (∑ k : Fin 2, WittVector.teichmuller p (d k) • η k) + E.verschiebung s =
        (∑ k : Fin 2, WittVector.teichmuller p (d k * u k) • ε k) +
          E.verschiebung (s + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (d k)) • w k) := by
    intro d s
    rw [show (∑ k : Fin 2, WittVector.teichmuller p (d k) • η k) =
        ∑ k : Fin 2, WittVector.teichmuller p (d k) •
          (WittVector.teichmuller p (u k) • ε k + E.verschiebung (w k)) from
      Finset.sum_congr rfl (fun k _ => by rw [K k])]
    exact recombine E d u ε w s
  have hu0 := (hε.2 _).unique (y₁ := (fun k => c k * u k, _)) (y₂ := (fun k => c' k * u k, _))
    (H c y) (h.trans (H c' y'))
  have hcu : ∀ k, c k * u k = c' k * u k := fun k => congrFun (congrArg Prod.fst hu0) k
  have hc : c = c' := funext fun k => by
    have := congrArg (fun r => r * v k) (hcu k)
    simp only [mul_assoc, mul_comm (u k) (v k), hvu k, mul_one] at this
    exact this
  subst hc
  exact ⟨rfl, add_right_cancel (congrArg Prod.snd hu0)⟩

end P2mVbt

end

open P2mVbt in
theorem solution
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B} (φ : S →+* B)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : DS.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D f)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ) :
    D.IsHomogeneousVBasis (fun i => f (γ i)) := by
  obtain ⟨δ, hδS, hδ⟩ := hf.2.2.2.2.2
  have hfs := hf.1
  have hfV := hf.2.2.1
  have hfp := hf.2.2.2.2.1
  choose a z ha using fun i => diag DS γ δ hγ.1 hδS i
  choose b t hb using fun i => diag DS δ γ hδS.1 hγ i
  have hba : ∀ i, b i * a i = 1 := fun i =>
    unit_of_diag DS γ δ hδS i (a i) (b i) (z i) (t i) (ha i) (hb i)
  have K : ∀ i, f (γ i) = WittVector.teichmuller p (φ (a i)) • f (δ i) + D.verschiebung (f (z i)) :=
    fun i => by rw [ha i, map_add, hfs, WittVector.map_teichmuller, hfV]
  have K' : ∀ i, f (δ i) = WittVector.teichmuller p (φ (b i)) • f (γ i) + D.verschiebung (f (t i)) :=
    fun i => by rw [hb i, map_add, hfs, WittVector.map_teichmuller, hfV]
  have hvu : ∀ i, φ (b i) * φ (a i) = 1 := fun i => by rw [← map_mul, hba i, map_one]
  refine ⟨fun i => hfp i _ (hγ.1 i), fun x => ?_⟩
  obtain ⟨c, y, hx⟩ := expand_exists D (ε := fun i => f (δ i)) (η := fun i => f (γ i)) hδ
    (v := fun i => φ (b i)) (w := fun i => f (t i)) K' x
  refine ⟨(c, y), hx, ?_⟩
  rintro ⟨c', y'⟩ hx'
  obtain ⟨hc, hy⟩ := expand_unique D (ε := fun i => f (δ i)) (η := fun i => f (γ i)) hδ
    (u := fun i => φ (a i)) (v := fun i => φ (b i)) (w := fun i => f (z i)) K hvu c' y' c y
    (hx'.symm.trans hx)
  exact Prod.ext hc hy

end S_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_isHomogeneousVBasis_map_of_baseChange (solution)
