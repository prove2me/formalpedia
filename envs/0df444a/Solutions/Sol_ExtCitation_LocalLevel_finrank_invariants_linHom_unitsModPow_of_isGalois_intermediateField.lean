-- Prove2me | solution 1 for ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ffbdb281-5438-50be-825a-459354dd0b78

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis
import Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open Module
open scoped IntermediateField Pointwise

set_option synthInstance.maxHeartbeats 1600000 in
open ExtCitation.LocalLevel _root_.IsLocalRing _root_.Module.IsLocalRing in

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod p) VPF] (PF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ p = u)
    (hπFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (σ : Kw →* Kw) u)) = PF σ (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod p) VTF] (TF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ p = 1)
    (hιFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (v : VTF),
      Additive.toMul (ιF (TF σ v)) = Units.map (σ : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod p) (N.linHom PF).invariants
      = Module.finrank ℚ_[p] K * finrank (ZMod p) VN + finrank (ZMod p) (N.linHom TF).invariants
        + finrank (ZMod p) (N.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))).invariants := by
  classical
  let Kw' : IntermediateField ℚ_[p] (PadicAlgCl p) := Kw.restrictScalars ℚ_[p]
  haveI hKw'fd : FiniteDimensional ℚ_[p] Kw' := by
    show FiniteDimensional ℚ_[p] Kw
    exact FiniteDimensional.trans ℚ_[p] K Kw
  let act : (Kw ≃ₐ[K] Kw) →* (Kw' ≃ₐ[ℚ_[p]] Kw') :=
    { toFun := fun σ => (σ.restrictScalars ℚ_[p] : Kw ≃ₐ[ℚ_[p]] Kw)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hact : ∀ (σ : Kw ≃ₐ[K] Kw) (x : Kw), act σ (show Kw' from x) = (show Kw' from σ x) := fun _ _ => rfl
  have hΔcard : ¬ p ∣ Fintype.card (Kw ≃ₐ[K] Kw) := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact htame

  have hmemRw : ∀ x : Kw', x ∈ Rw p Kw' ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
    intro x
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  have hscale : ∀ x : PadicAlgCl p, ∃ N : ℕ, ‖algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℚ_[p]) ^ N) * x‖ ≤ 1 := by
    intro x
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖x‖ (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_algebraMap', norm_pow, Padic.norm_p]
    have hqpos : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) N
    rw [inv_pow, inv_mul_le_iff₀ hqpos, mul_one]
    exact hN.le
  have hp0 : ∀ N : ℕ, ((p : ℚ_[p]) ^ N) ≠ 0 := fun N => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hKsmul : ∀ (c : K) (x : Kw), ((c • x : Kw) : PadicAlgCl p) = (c : PadicAlgCl p) * (x : PadicAlgCl p) :=
    fun c x => by rw [Algebra.smul_def]; rfl
  have hQsmulK : ∀ (c : ℚ_[p]) (x : K), ((c • x : K) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) c * (x : PadicAlgCl p) :=
    fun c x => by rw [Algebra.smul_def]; rfl
  have hσsmul : ∀ (σ : Kw ≃ₐ[K] Kw) (c : K) (x : Kw), σ (c • x) = c • σ x := fun σ c x => by
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]

  let b₀ := IsGalois.normalBasis K Kw
  obtain ⟨N₁, hN₁⟩ := hscale ((b₀ 1 : Kw) : PadicAlgCl p)
  let c₁ : K := algebraMap ℚ_[p] K ((p : ℚ_[p]) ^ N₁)
  have hc₁ : (c₁ : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℚ_[p]) ^ N₁) := rfl
  have hc₁u : IsUnit c₁ := (IsUnit.mk0 _ (hp0 N₁)).map (algebraMap ℚ_[p] K)
  let θ : Kw := c₁ • b₀ 1
  let bθ : Module.Basis (Kw ≃ₐ[K] Kw) K Kw := b₀.isUnitSMul (fun _ => hc₁u)
  have hbθ : ∀ σ, bθ σ = σ θ := by
    intro σ
    rw [Module.Basis.isUnitSMul_apply, IsGalois.normalBasis_apply σ, hσsmul]
  have hθR : ∀ σ : Kw ≃ₐ[K] Kw, (show Kw' from σ θ) ∈ Rw p Kw' := by
    intro σ
    rw [← hact, algEquiv_apply_mem_Rw_iff p Kw' (act σ), hmemRw]
    show ‖((c₁ • b₀ 1 : Kw) : PadicAlgCl p)‖ ≤ 1
    rw [hKsmul, hc₁]
    exact hN₁

  let bK₀ := Module.finBasis ℚ_[p] K
  choose NK hNK using fun i => hscale ((bK₀ i : K) : PadicAlgCl p)
  let bK : Module.Basis (Fin (Module.finrank ℚ_[p] K)) ℚ_[p] K :=
    bK₀.isUnitSMul (fun i => IsUnit.mk0 _ (hp0 (NK i)))
  have hbK : ∀ i, bK i = ((p : ℚ_[p]) ^ NK i) • bK₀ i := fun i => by rw [Module.Basis.isUnitSMul_apply]
  have hbKR : ∀ i, ‖((bK i : K) : PadicAlgCl p)‖ ≤ 1 := by
    intro i; rw [hbK, hQsmulK]; exact hNK i

  let B : Module.Basis (Fin (Module.finrank ℚ_[p] K) × (Kw ≃ₐ[K] Kw)) ℚ_[p] Kw := bK.smulTower bθ
  have hB : ∀ i σ, B (i, σ) = bK i • bθ σ := fun i σ => Module.Basis.smulTower_apply bK bθ (i, σ)
  let w : (Kw ≃ₐ[K] Kw) × Fin (Module.finrank ℚ_[p] K) → Kw' := fun x => show Kw' from B (x.2, x.1)
  have hwval : ∀ (σ : Kw ≃ₐ[K] Kw) (i : Fin (Module.finrank ℚ_[p] K)),
      ((w (σ, i) : Kw') : PadicAlgCl p) = ((bK i : K) : PadicAlgCl p) * ((σ θ : Kw) : PadicAlgCl p) := by
    intro σ i
    show ((B (i, σ) : Kw) : PadicAlgCl p) = _
    rw [hB, hbθ]
    show (((bK i : K) • σ θ : Kw) : PadicAlgCl p) = _
    rw [hKsmul]
  have hwR : ∀ x, w x ∈ Rw p Kw' := by
    rintro ⟨σ, i⟩
    rw [hmemRw, hwval, norm_mul]
    exact mul_le_one₀ (hbKR i) (norm_nonneg _) ((hmemRw _).mp (hθR σ))
  have hw : LinearIndependent ℚ_[p] w :=
    B.linearIndependent.comp (fun x : (Kw ≃ₐ[K] Kw) × Fin (Module.finrank ℚ_[p] K) => (x.2, x.1))
      (fun x y h => by
        have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
        exact Prod.ext h2 h1)
  have hcardw : Fintype.card ((Kw ≃ₐ[K] Kw) × Fin (Module.finrank ℚ_[p] K)) = Module.finrank ℚ_[p] Kw' := by
    show _ = Module.finrank ℚ_[p] Kw
    rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      mul_comm, Module.finrank_mul_finrank]
  have hperm : ∀ (d d' : Kw ≃ₐ[K] Kw) (i : Fin (Module.finrank ℚ_[p] K)), act d (w (d', i)) = w (d * d', i) := by
    intro d d' i
    show (show Kw' from d (B (i, d'))) = (show Kw' from B (i, d * d'))
    congr 1
    rw [hB, hB, hbθ, hbθ, hσsmul, AlgEquiv.mul_apply]
  have key := ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis p Kw' hΔcard act
    w hwR hw hcardw hperm N PF πF hπF hkerπF (fun d u => hπFΔ d u) TF ιF hιF hranιF (fun d u => hιFΔ d u)
  rw [Fintype.card_fin] at key
  exact key

end S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
end P2MW
export P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField (solution)
