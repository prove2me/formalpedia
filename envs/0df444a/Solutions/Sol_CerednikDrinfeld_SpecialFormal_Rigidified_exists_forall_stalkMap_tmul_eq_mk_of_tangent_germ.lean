-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fa3fd866-ec5e-5e14-a5a8-01f8ac1e7c73

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace StalkPi

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nVarpi_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nsmul_nMk (D : GradedCartierModuleData p B j) (k : ℕ) (m m' : D.M) :
    k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) :
    D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, nsmul_nMk]

theorem toLieQuot_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.toLieQuot (D.nMk (m, m')) = D.vRange.mkQ m := rfl

theorem nVarpi_mem_etaPiece (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (z : D.NMod)
    (hz : z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i) :
    D.nVarpi z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung (i + 1) := by
  obtain ⟨hfix, hpiece⟩ := AddSubgroup.mem_inf.mp hz
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hpiece
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_eta_iff] at hfix ⊢
    rw [nVarpi_nMk, phi_nMk,
      CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi p j D hD L hL a]
    have h0 : D.nMk (D.varpi b, 0) = D.nVarpi (D.nMk (b, 0)) := by rw [nVarpi_nMk, map_zero]
    rw [h0, ← map_add, ← phi_nMk D L hL.isCartierLMap.map_verschiebung a b, hfix, nVarpi_nMk]
  · rw [nVarpi_nMk]
    exact AddSubgroup.mem_map.mpr ⟨(D.varpi a, D.varpi b),
      AddSubgroup.mem_prod.mpr ⟨D.varpi_mem i a ha, D.varpi_mem i b hb⟩, rfl⟩

theorem mkQ_varpi_eq_toLieQuot_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) (m : D.M)
    (hm : D.vRange.mkQ m = D.toLieQuot z) :
    D.vRange.mkQ (D.varpi m) = D.toLieQuot (D.nVarpi z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [toLieQuot_nMk] at hm
  rw [nVarpi_nMk, toLieQuot_nMk]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hm ⊢
  obtain ⟨y, hy⟩ := (D.mem_vRange_iff _).mp hm
  exact (D.mem_vRange_iff _).mpr ⟨D.varpi y, by rw [← D.varpi_verschiebung, hy, map_sub]⟩

theorem latticeRel_nsmul (D : GradedCartierModuleData p B j) {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ D.NMod}
    {zbar : D.NMod} {v : Fin 2 → ℚ_[p]} (h : Rigidified.LatticeRel D n r zbar v) :
    Rigidified.LatticeRel D n r ((p : ℕ) • zbar) ((p : ℚ_[p]) • v) := by
  obtain ⟨m, k, w, hw, hrel⟩ := h
  refine ⟨m, k, (p : ℕ) • w, ?_, ?_⟩
  · rw [smul_comm, hw]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, PadicInt.coe_mul, PadicInt.coe_natCast]
    rfl
  · rw [map_nsmul, smul_comm (p ^ k), hrel]
    exact smul_comm _ _ _

end Datum

section Tangent

variable {p : ℕ} [Fact p.Prime]

theorem tangent_eq_of_mkQ_eq {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1)) (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData jS hc).vRange.mkQ m = (X.toGradedCartierModuleData jS hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData jS hc).mem_vRange_iff _).mp h
  have hy' : verschiebungInt y = m - m' := hy
  have : tangent (m - m') = 0 := by
    rw [← hy']
    exact tangent_verschiebungInt y
  rwa [map_sub, sub_eq_zero] at this

theorem tangent_varpi {B S : Type} [CommRing B] [CommRing S] (X : FormalODModule p B) (g : B →+* S)
    (m : CartierModule p (X.map g).F) :
    tangent (endAct (X.map g).varpiEnd m) = ((linearPart X.varpi).map g).mulVec (tangent m) := by
  have hL : linearPart (X.map g).varpiEnd.toPowerSeries = (linearPart X.varpi).map g := by
    ext i k
    simp only [linearPart, Matrix.of_apply, Matrix.map_apply]
    exact MvPowerSeries.coeff_map _ _ _
  rw [endAct_apply, tangent_map, hL]

end Tangent

section Loc

theorem mk_eq_map_mk {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal)
    (P Q : Submodule B (Fin 2 → B)) (Pi : ↥P →ₗ[B] ↥Q) (A : Matrix (Fin 2) (Fin 2) B)
    (hPi : ∀ s : ↥P, ((Pi s : ↥Q) : Fin 2 → B) = A.mulVec (s : Fin 2 → B))
    (s : ↥P) (b : x.asIdeal.primeCompl) (τ : Fin 2 → Rigidified.Baway f)
    (hs : ∀ i, Rigidified.locHom x ((s : Fin 2 → B) i) = Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (τ i))
    (s' : ↥Q) (b' : x.asIdeal.primeCompl)
    (hs' : ∀ i, Rigidified.locHom x ((s' : Fin 2 → B) i) =
      Rigidified.locHom x (b' : B) * Rigidified.awayToLoc x f hf ((A.map (Rigidified.awayHom f)).mulVec τ i)) :
    LocalizedModule.mk s' b' = LocalizedModule.map x.asIdeal.primeCompl Pi (LocalizedModule.mk s b) := by
  rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]

  have key : ∀ i, Rigidified.locHom x ((b : B) * (s' : Fin 2 → B) i) =
      Rigidified.locHom x ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i) := by
    intro i
    have hA : Rigidified.locHom x (A.mulVec (s : Fin 2 → B) i) =
        Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf ((A.map (Rigidified.awayHom f)).mulVec τ i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : Rigidified.awayToLoc x f hf (Rigidified.awayHom f (A i k)) = Rigidified.locHom x (A i k) := by
        unfold Rigidified.awayToLoc
        exact IsLocalization.Away.lift_eq f _ (A i k)
      rw [hk]; ring
    rw [map_mul, map_mul, hs', hPi, hA]; ring
  have key' : ∀ i, ∃ c : x.asIdeal.primeCompl,
      (c : B) * ((b : B) * (s' : Fin 2 → B) i) = (c : B) * ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i) :=
    fun i => (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)).mp (key i)
  obtain ⟨c₀, hc₀⟩ := key' 0
  obtain ⟨c₁, hc₁⟩ := key' 1
  refine ⟨c₀ * c₁, ?_⟩
  apply Subtype.ext
  funext i
  change ((c₀ : B) * c₁) * ((b : B) * (s' : Fin 2 → B) i) =
    ((c₀ : B) * c₁) * ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i)
  fin_cases i
  · simp only [Fin.zero_eta]
    linear_combination (c₁ : B) * hc₀
  · simp only [Fin.mk_one]
    linear_combination (c₀ : B) * hc₁

end Loc

end StalkPi

namespace StalkCont

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem awayToLoc_algebraMap {B : Type} [CommRing B] (y : PrimeSpectrum B) (f₀ : B) (hf₀ : f₀ ∉ y.asIdeal) (b : B) :
    Rigidified.awayToLoc y f₀ hf₀ (algebraMap B (Rigidified.Baway f₀) b) = Rigidified.locHom y b := by
  unfold Rigidified.awayToLoc
  exact IsLocalization.Away.lift_eq f₀ _ b

theorem not_mem_of_mul_not_mem_left {B : Type} [CommRing B] {y : PrimeSpectrum B} {a b : B}
    (h : a * b ∉ y.asIdeal) : a ∉ y.asIdeal := fun ha => h (y.asIdeal.mul_mem_right b ha)

theorem not_mem_of_mul_not_mem_right {B : Type} [CommRing B] {y : PrimeSpectrum B} {a b : B}
    (h : a * b ∉ y.asIdeal) : b ∉ y.asIdeal := fun hb => h (y.asIdeal.mul_mem_left a hb)

theorem cont_core {B : Type} [CommRing B] (x : PrimeSpectrum B) (P : Submodule B (Fin 2 → B))
    (f₀ : B) (hf₀ : f₀ ∉ x.asIdeal) (τ : Fin 2 → Rigidified.Baway f₀)
    (sx : ↥P) (bx : x.asIdeal.primeCompl)
    (hsx : ∀ i, Rigidified.locHom x ((sx : Fin 2 → B) i) =
      Rigidified.locHom x (bx : B) * Rigidified.awayToLoc x f₀ hf₀ (τ i)) :
    ∃ (f : B) (s : ↥P), f ∉ x.asIdeal ∧ (∀ y : PrimeSpectrum B, f ∉ y.asIdeal → f₀ ∉ y.asIdeal) ∧
      ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal) (hf₀y : f₀ ∉ y.asIdeal) (sy : ↥P)
        (by_ : y.asIdeal.primeCompl),
        (∀ i, Rigidified.locHom y ((sy : Fin 2 → B) i) =
          Rigidified.locHom y (by_ : B) * Rigidified.awayToLoc y f₀ hf₀y (τ i)) →
        LocalizedModule.mk sy by_ = LocalizedModule.mk s ⟨f, hy⟩ := by

  obtain ⟨⟨a₀, d₀⟩, h₀⟩ := IsLocalization.surj (Submonoid.powers f₀) (τ 0)
  obtain ⟨⟨a₁, d₁⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers f₀) (τ 1)
  obtain ⟨n₀, hn₀⟩ := (Submonoid.mem_powers_iff _ _).mp d₀.2
  obtain ⟨n₁, hn₁⟩ := (Submonoid.mem_powers_iff _ _).mp d₁.2
  have hd : ∀ y : PrimeSpectrum B, f₀ ∉ y.asIdeal → (d₀ : B) * (d₁ : B) ∉ y.asIdeal := by
    intro y hy hdy
    rw [← hn₀, ← hn₁, ← pow_add] at hdy
    exact hy (y.isPrime.mem_of_pow_mem _ hdy)

  have hτ0 : ∀ (y : PrimeSpectrum B) (hf₀y : f₀ ∉ y.asIdeal),
      Rigidified.awayToLoc y f₀ hf₀y (τ 0) * Rigidified.locHom y ((d₀ : B) * (d₁ : B)) =
        Rigidified.locHom y (a₀ * (d₁ : B)) := by
    intro y hf₀y
    have := congrArg (Rigidified.awayToLoc y f₀ hf₀y) h₀
    rw [map_mul, awayToLoc_algebraMap, awayToLoc_algebraMap] at this
    rw [map_mul, map_mul, ← mul_assoc, this]
  have hτ1 : ∀ (y : PrimeSpectrum B) (hf₀y : f₀ ∉ y.asIdeal),
      Rigidified.awayToLoc y f₀ hf₀y (τ 1) * Rigidified.locHom y ((d₀ : B) * (d₁ : B)) =
        Rigidified.locHom y (a₁ * (d₀ : B)) := by
    intro y hf₀y
    have := congrArg (Rigidified.awayToLoc y f₀ hf₀y) h₁
    rw [map_mul, awayToLoc_algebraMap, awayToLoc_algebraMap] at this
    rw [map_mul, map_mul, mul_comm (Rigidified.locHom y (d₀ : B)), ← mul_assoc, this]

  have germ : ∀ (y : PrimeSpectrum B) (hf₀y : f₀ ∉ y.asIdeal) (sy : ↥P) (by_ : y.asIdeal.primeCompl),
      (∀ i, Rigidified.locHom y ((sy : Fin 2 → B) i) =
        Rigidified.locHom y (by_ : B) * Rigidified.awayToLoc y f₀ hf₀y (τ i)) →
      ∃ e : y.asIdeal.primeCompl,
        (e : B) * ((sy : Fin 2 → B) 0 * ((d₀ : B) * (d₁ : B))) = (e : B) * ((by_ : B) * (a₀ * (d₁ : B))) ∧
        (e : B) * ((sy : Fin 2 → B) 1 * ((d₀ : B) * (d₁ : B))) = (e : B) * ((by_ : B) * (a₁ * (d₀ : B))) := by
    intro y hf₀y sy by_ hsy
    have k0 : Rigidified.locHom y ((sy : Fin 2 → B) 0 * ((d₀ : B) * (d₁ : B))) =
        Rigidified.locHom y ((by_ : B) * (a₀ * (d₁ : B))) := by
      rw [map_mul, hsy 0, mul_assoc, hτ0 y hf₀y, ← map_mul]
    have k1 : Rigidified.locHom y ((sy : Fin 2 → B) 1 * ((d₀ : B) * (d₁ : B))) =
        Rigidified.locHom y ((by_ : B) * (a₁ * (d₀ : B))) := by
      rw [map_mul, hsy 1, mul_assoc, hτ1 y hf₀y, ← map_mul]
    obtain ⟨e₀, he₀⟩ := (IsLocalization.eq_iff_exists y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)).mp k0
    obtain ⟨e₁, he₁⟩ := (IsLocalization.eq_iff_exists y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)).mp k1
    refine ⟨e₀ * e₁, ?_, ?_⟩
    · simp only [Submonoid.coe_mul]; linear_combination (e₁ : B) * he₀
    · simp only [Submonoid.coe_mul]; linear_combination (e₀ : B) * he₁

  obtain ⟨c, hc0, hc1⟩ := germ x hf₀ sx bx hsx
  refine ⟨f₀ * ((bx : B) * (c : B)), (f₀ * (c : B)) • sx, ?_, fun y hy => not_mem_of_mul_not_mem_left hy, ?_⟩
  · intro hmem
    rcases x.isPrime.mem_or_mem hmem with h | h
    · exact hf₀ h
    rcases x.isPrime.mem_or_mem h with h | h
    · exact bx.2 h
    · exact c.2 h
  intro y hy hf₀y sy by_ hsy
  have hbx : (bx : B) ∉ y.asIdeal := not_mem_of_mul_not_mem_left (not_mem_of_mul_not_mem_right hy)
  have hcy : (c : B) ∉ y.asIdeal := not_mem_of_mul_not_mem_right (not_mem_of_mul_not_mem_right hy)
  obtain ⟨e, he0, he1⟩ := germ y hf₀y sy by_ hsy
  rw [LocalizedModule.mk_eq]
  refine ⟨e * ⟨(d₀ : B) * (d₁ : B), hd y hf₀y⟩ * ⟨(c : B), hcy⟩, ?_⟩
  apply Subtype.ext
  funext i
  change ((e : B) * ((d₀ : B) * (d₁ : B)) * (c : B)) * ((f₀ * ((bx : B) * (c : B))) * (sy : Fin 2 → B) i) =
    ((e : B) * ((d₀ : B) * (d₁ : B)) * (c : B)) * ((by_ : B) * ((f₀ * (c : B)) * (sx : Fin 2 → B) i))
  fin_cases i
  · simp only [Fin.zero_eta]
    linear_combination (f₀ * (bx : B) * (c : B) * (c : B)) * he0 - (f₀ * (by_ : B) * (e : B) * (c : B)) * hc0
  · simp only [Fin.mk_one]
    linear_combination (f₀ * (bx : B) * (c : B) * (c : B)) * he1 - (f₀ * (by_ : B) * (e : B) * (c : B)) * hc1

end StalkCont

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i))) :
    (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x →
          ∃ (f : B) (s : ↥(t.X.lieZero (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₀ y, u₀ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x →
          ∃ (f : B) (s : ↥(t.X.lieOne (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₁ y, u₁ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk s ⟨f, hy⟩) := by
  refine ⟨fun x v hv => ?_, fun x v hv => ?_⟩
  · obtain ⟨f₀, hf₀, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₀ x v).mp hv
    obtain ⟨mx, sx, bx, hmx, hux, hsx⟩ := hg₀ x v hv f₀ hf₀ hc hcb hcΦf L hL z hz
    obtain ⟨f, s, hfx, hf₀_of, H⟩ :=
      StalkCont.cont_core x _ f₀ hf₀ (MvFormalGroup.CartierModule.tangent mx) sx bx hsx
    refine ⟨f, s, hfx, fun y hy => ?_⟩
    have hf₀y := hf₀_of y hy
    have hvy : v ∈ N₀ y := (hN₀ y v).mpr ⟨f₀, hf₀y, hc, hcb, hcΦf, L, hL, z, hz⟩
    refine ⟨hvy, ?_⟩
    obtain ⟨my, sy, by_, hmy, huy, hsy⟩ := hg₀ y v hvy f₀ hf₀y hc hcb hcΦf L hL z hz
    rw [huy]
    have htan : MvFormalGroup.CartierModule.tangent my = MvFormalGroup.CartierModule.tangent mx :=
      StalkPi.tangent_eq_of_mkQ_eq (t.XS (Rigidified.awayHom f₀)) (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hc
        my mx (hmy.trans hmx.symm)
    exact H y hy hf₀y sy by_ (fun i => by rw [← htan]; exact hsy i)
  · obtain ⟨f₀, hf₀, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₁ x v).mp hv
    obtain ⟨mx, sx, bx, hmx, hux, hsx⟩ := hg₁ x v hv f₀ hf₀ hc hcb hcΦf L hL z hz
    obtain ⟨f, s, hfx, hf₀_of, H⟩ :=
      StalkCont.cont_core x _ f₀ hf₀ (MvFormalGroup.CartierModule.tangent mx) sx bx hsx
    refine ⟨f, s, hfx, fun y hy => ?_⟩
    have hf₀y := hf₀_of y hy
    have hvy : v ∈ N₁ y := (hN₁ y v).mpr ⟨f₀, hf₀y, hc, hcb, hcΦf, L, hL, z, hz⟩
    refine ⟨hvy, ?_⟩
    obtain ⟨my, sy, by_, hmy, huy, hsy⟩ := hg₁ y v hvy f₀ hf₀y hc hcb hcΦf L hL z hz
    rw [huy]
    have htan : MvFormalGroup.CartierModule.tangent my = MvFormalGroup.CartierModule.tangent mx :=
      StalkPi.tangent_eq_of_mkQ_eq (t.XS (Rigidified.awayHom f₀)) (Rigidified.jS ι ψ (Rigidified.awayHom f₀)) hc
        my mx (hmy.trans hmx.symm)
    exact H y hy hf₀y sy by_ (fun i => by rw [← htan]; exact hsy i)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ (solution)
