-- Prove2me | solution 1 for Deformation.exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a9b080f0-a66c-5def-bf09-34dab83e701d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector
import Theorems.Thm_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector
import Theorems.Thm_Deformation_map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace S17L2

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

theorem pow_sub_self_mem [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (c : 𝓞) :
    c ^ p - c ∈ Ideal.span {(p : 𝓞)} := by
  rw [← hker, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]

open Classical in

noncomputable def pin (N : ℕ) {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞) (m : Fin d →₀ ℕ) : 𝓞 :=
  if m.degree ≤ N then (p : 𝓞) ^ (N - m.degree) * φi.coeff m
  else if h : (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m then Classical.choose h else 0

omit [Fact p.Prime] in
open Classical in
theorem pin_spec (N : ℕ) {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞) (m : Fin d →₀ ℕ) :
    (m.degree ≤ N → pin p N φi m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
    (N < m.degree → pin p N φi m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
      (pin p N φi m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m)) := by
  constructor
  · intro h; rw [pin, if_pos h]
  · intro h
    rw [pin, if_neg (not_le.2 h)]
    by_cases hd : (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m
    · left
      rw [dif_pos hd, mul_comm]
      exact (Classical.choose_spec hd).symm
    · right
      exact ⟨by rw [dif_neg hd], hd⟩

theorem ghostComponent_map {R : Type v} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f x) = f (WittVector.ghostComponent n x) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, MvPolynomial.aeval_def,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem main
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i : Fin d,
      ∃ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N →
            (WittVector.ghostComponent (N - 1) ℓ).coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree →
            (WittVector.ghostComponent (N - 1) ℓ).coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
              ((WittVector.ghostComponent (N - 1) ℓ).coeff m = 0 ∧
                ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) ∧
        WittVector.truncate N (WittVector.map
            ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
              π.toRingHom) ℓ) ∈
          Deformation.wittHom (ZMod p) p N (TensorProduct 𝓞 (ZMod p) R) ∧
        WittVector.truncate N (WittVector.map
            ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
              π.toRingHom) ℓ) ∈
          Deformation.TruncWitt.fontaineKer p N
            (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom := by
  classical
  have hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)} := pow_sub_self_mem p hker
  have hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree} :=
    fun i j m => MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m
  obtain ⟨N₀, hN₀⟩ := Deformation.truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector
    p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip
  obtain ⟨N₁, hN₁⟩ := Deformation.map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup
    p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip
  refine ⟨max (max N₀ N₁) 1, fun N hN i => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN

  obtain ⟨ℓ, hℓ⟩ := MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_logCovector
    p hp hfrob (φ i) (hint i) N (pin p N (φ i)) (pin_spec p N (φ i))
  have htop : ∀ m : Fin d →₀ ℕ, (WittVector.ghostComponent (N - 1) ℓ).coeff m = pin p N (φ i) m := by
    intro m
    have h := hℓ (N - 1) (by omega) m
    rw [h, show N - 1 - (N - 1) = 0 from Nat.sub_self _, pow_zero, one_smul]
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro m
    have hs := pin_spec p N (φ i) m
    rw [← htop m] at hs
    exact hs
  · exact hN₀ N hN0 i (pin p N (φ i)) (pin_spec p N (φ i)) ℓ hℓ
  ·
    have hG : π (WittVector.ghostComponent (N - 1) ℓ) ∈ Ideal.span {(p : R) ^ N} :=
      hN₁ N hN1 i _ (fun m => by have hs := pin_spec p N (φ i) m; rw [← htop m] at hs; exact hs)
    refine ⟨WittVector.map π.toRingHom ℓ, ?_, ?_⟩
    · ext k
      simp only [WittVector.coeff_truncate, WittVector.map_coeff, RingHom.comp_apply]
    · rw [S17L2.ghostComponent_map]
      exact hG

end S17L2

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i : Fin d,
      ∃ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N →
            (WittVector.ghostComponent (N - 1) ℓ).coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree →
            (WittVector.ghostComponent (N - 1) ℓ).coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
              ((WittVector.ghostComponent (N - 1) ℓ).coeff m = 0 ∧
                ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) ∧
        WittVector.truncate N (WittVector.map
            ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
              π.toRingHom) ℓ) ∈
          Deformation.wittHom (ZMod p) p N (TensorProduct 𝓞 (ZMod p) R) ∧
        WittVector.truncate N (WittVector.map
            ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
              π.toRingHom) ℓ) ∈
          Deformation.TruncWitt.fontaineKer p N
            (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom :=
  S17L2.main p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip

end S_Deformation_exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup
end P2MW
export P2MW.S_Deformation_exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup (solution)
