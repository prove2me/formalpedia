-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.pullback_of_isTranslateOdd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8b4f17d0-af4f-596e-be83-f1746fb673db

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalOmega.DrinfeldDatum TensorProduct Matrix

noncomputable section

namespace P2mKcQuadrupleOdd

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (C : Type) [CommRing C] [Algebra 𝒪 C]

section Psi

variable {C}
variable (γ h : GL (Fin 2) K) (hγh : γ * h = 1)
include hγh

theorem mulVec_mulVec_γh (v : Fin 2 → K) : (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hγh, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_hγ (v : Fin 2 → K) : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ ((γ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v := by
  have hhγ : h * γ = 1 := by rw [eq_inv_of_mul_eq_one_right hγh, inv_mul_cancel]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hhγ, Units.val_one, Matrix.one_mulVec]

theorem act_act_val (L : FullLattice 𝒪 K) : (FullLattice.act γ (FullLattice.act h L)).1 = L.1 := by
  show latticeMap γ (latticeMap h L.1) = L.1
  rw [← latticeMap_mul, hγh, latticeMap_one]

variable (C)

def Psi (L : FullLattice 𝒪 K) : latticeBaseChange 𝒪 K C (FullLattice.act h L) ≃ₗ[C] latticeBaseChange 𝒪 K C L :=
  (actBaseChange C γ (FullLattice.act h L)).trans (transportEquiv C (act_act_val γ h hγh L))

theorem Psi_tmul (L : FullLattice 𝒪 K) (b : C) (w : ↥(FullLattice.act h L).1) :
    Psi C γ h hγh L (b ⊗ₜ[𝒪] w) =
      b ⊗ₜ[𝒪] (⟨(γ : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K), (act_act_val γ h hγh L).le (mulVec_mem_latticeMap w.2)⟩ : ↥L.1) :=
  rfl

variable {C}

theorem line_pullback_act (d : DeligneDatum (K := K) π C) (L : FullLattice 𝒪 K) :
    (DeligneDatum.pullback π C γ d).line (FullLattice.act h L) = (d.line L).comap (Psi C γ h hγh L).toLinearMap := by
  show (d.line (FullLattice.act γ (FullLattice.act h L))).comap (actBaseChange C γ (FullLattice.act h L)).toLinearMap = _
  rw [DeligneDatum.line_transport π d (act_act_val γ h hγh L), Psi]
  ext z
  simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  constructor
  · intro hz; exact ⟨_, hz, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    rwa [← (transportEquiv C (act_act_val γ h hγh L)).injective hyz]

theorem psi_mem_sup (d : DeligneDatum (K := K) π C) (L : FullLattice 𝒪 K) (𝔭 : Ideal C) (z : latticeBaseChange 𝒪 K C (FullLattice.act h L))
    (hz : z ∈ (DeligneDatum.pullback π C γ d).line (FullLattice.act h L) ⊔ (𝔭 • ⊤ : Submodule C (latticeBaseChange 𝒪 K C (FullLattice.act h L)))) :
    Psi C γ h hγh L z ∈ d.line L ⊔ (𝔭 • ⊤ : Submodule C (latticeBaseChange 𝒪 K C L)) := by
  obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · rw [line_pullback_act π γ h hγh d L, Submodule.mem_comap] at hy
    exact hy
  · refine Submodule.smul_induction_on (p := fun z' => Psi C γ h hγh L z' ∈ (𝔭 • ⊤ : Submodule C (latticeBaseChange 𝒪 K C L))) hz'
      (fun r hr n _ => ?_) (fun a b ha hb => ?_)
    · show Psi C γ h hγh L (r • n) ∈ _
      rw [LinearEquiv.map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · show Psi C γ h hγh L (a + b) ∈ _
      rw [LinearEquiv.map_add]; exact Submodule.add_mem _ ha hb

end Psi

section Edge

variable {C}
variable (γ h : GL (Fin 2) K) (hγh : γ * h = 1)
include hγh

theorem edgeNondegAt_pullback (d : DeligneDatum (K := K) π C) (𝔭 : Ideal C) (L₀ L₁ : FullLattice 𝒪 K)
    (he : d.EdgeNondegAt π 𝔭 L₀ L₁) :
    (DeligneDatum.pullback π C γ d).EdgeNondegAt π 𝔭 (FullLattice.act h L₀) (FullLattice.act h L₁) := by
  obtain ⟨hle, hπ, h1, h2⟩ := he
  refine ⟨latticeMap_mono h hle, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    rw [← hwv, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
  · intro v hv hmem
    have hγv : (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K) ∈ L₁.1 :=
      (act_act_val γ h hγh L₁).le (mulVec_mem_latticeMap v.2)
    refine h1 ⟨_, hγv⟩ ?_ (psi_mem_sup π γ h hγh d L₁ 𝔭 _ hmem)
    intro hγv0
    apply hv
    have h' := mulVec_mem_latticeMap (g := h) hγv0
    rwa [mulVec_mulVec_hγ γ h hγh] at h'
  · intro v' hv' hmem
    have hγv' : (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ (v' : Fin 2 → K) ∈ L₀.1 :=
      (act_act_val γ h hγh L₀).le (mulVec_mem_latticeMap v'.2)
    refine h2 ⟨_, hγv'⟩ ?_ (psi_mem_sup π γ h hγh d L₀ 𝔭 _ hmem)
    rintro ⟨w, hw⟩
    apply hv'
    refine ⟨⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K), mulVec_mem_latticeMap w.2⟩, ?_⟩
    show (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K))
    rw [← Matrix.mulVec_smul, ← hw, mulVec_mulVec_hγ γ h hγh]

end Edge

section Kernel

variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (γ h : GL (Fin 2) K) (hγh : γ * h = 1) (x : PrimeSpectrum B)

omit hγh in

theorem ext_one_tmul {C : Type} [CommRing C] [Algebra 𝒪 C] {M : FullLattice 𝒪 K} {P : Type} [AddCommGroup P] [Module C P]
    (u u' : latticeBaseChange 𝒪 K C M →ₗ[C] P) (huu' : ∀ v : ↥M.1, u ((1 : C) ⊗ₜ[𝒪] v) = u' ((1 : C) ⊗ₜ[𝒪] v)) : u = u' := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c v =>
    have hc : (c ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K C M) = c • ((1 : C) ⊗ₜ[𝒪] v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, huu']

include hγh in

theorem ker_transfer (L L' : FullLattice 𝒪 K) (hL' : L' = FullLattice.act h L)
    {T T' : Type} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T'] (τ : T ≃ₗ[B] T')
    (u : latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x T)
    (u' : latticeBaseChange 𝒪 K (locRing B x) L' →ₗ[locRing B x] stalk B x T')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ L.1) (hv' : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ L'.1),
      u' ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥L'.1)) =
        LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap (u ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥L.1))))
    (d : DeligneDatum (K := K) π B) (hker : LinearMap.ker u = (d.map π (toLocRing B x)).line L) :
    LinearMap.ker u' = ((DeligneDatum.pullback π B γ d).map π (toLocRing B x)).line L' := by
  subst hL'
  rw [DeligneDatum.map_pullback π (toLocRing B x) γ d, line_pullback_act π γ h hγh (d.map π (toLocRing B x)) L, ← hker]

  have key : ∀ z, u' z = LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap (u (Psi (locRing B x) γ h hγh L z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    | add a b ha hb => rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]
    | tmul r w =>
      obtain ⟨v, hv, hvw⟩ := mem_latticeMap.mp w.2
      have hw : w = ⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ v, mulVec_mem_latticeMap hv⟩ := Subtype.ext hvw.symm
      have hr : (r ⊗ₜ[𝒪] w : latticeBaseChange 𝒪 K (locRing B x) (FullLattice.act h L)) = r • ((1 : locRing B x) ⊗ₜ[𝒪] w) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hr, LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.map_smul, LinearMap.map_smul, Psi_tmul]
      have hγw : (⟨(γ : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K), (act_act_val γ h hγh L).le (mulVec_mem_latticeMap w.2)⟩ : ↥L.1) =
          ⟨v, hv⟩ := by
        apply Subtype.ext
        show (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K) = v
        rw [hw]; exact mulVec_mulVec_γh γ h hγh v
      rw [hγw, hw, hu v hv (mulVec_mem_latticeMap hv)]
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, key z, LinearEquiv.coe_coe]
  constructor
  · intro hz
    exact LocalizedModule.map_injective _ _ τ.injective (by rw [hz, map_zero])
  · intro hz; rw [hz, map_zero]

end Kernel

section Action

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem pullback_mul (a b : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (a * b) d = DeligneDatum.pullback π B b (DeligneDatum.pullback π B a d) := by
  have hab := (Omega.action K π).act_mul B b⁻¹ a⁻¹ d
  change DeligneDatum.pullback π B (b⁻¹ * a⁻¹)⁻¹ d = DeligneDatum.pullback π B b⁻¹⁻¹ (DeligneDatum.pullback π B a⁻¹⁻¹ d) at hab
  exact hab

theorem pullback_scalarGL (c : Kˣ) (d : DeligneDatum (K := K) π B) : DeligneDatum.pullback π B (scalarGL c) d = d := by
  apply DeligneDatum.ext'
  funext M
  show (d.line (FullLattice.act (scalarGL c) M)).comap (actBaseChange B (scalarGL c) M).toLinearMap = d.line M
  rw [d.homothety c M]
  ext z
  simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rwa [← (actBaseChange B (scalarGL c) M).injective hyz]
  · intro hz; exact ⟨z, hz, rfl⟩

theorem scalarGL_inv (c : Kˣ) : (scalarGL c : GL (Fin 2) K)⁻¹ = scalarGL c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one]

end Action

section Swap

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

abbrev piUnit (hπ : algebraMap 𝒪 K π ≠ 0) : Kˣ := Units.mk0 (algebraMap 𝒪 K π) hπ

theorem mem_act_pi_iff (hπ : algebraMap 𝒪 K π ≠ 0) (M : FullLattice 𝒪 K) (v : Fin 2 → K) :
    v ∈ (FullLattice.act (scalarGL (piUnit π hπ)) M).1 ↔ ∃ w : ↥M.1, v = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  show v ∈ latticeMap (scalarGL (piUnit π hπ)) M.1 ↔ _
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨w, rfl⟩; exact ⟨w, w.2, rfl⟩

variable {B}

theorem tmul_mem_of_tmul_smul_mem (hπ : algebraMap 𝒪 K π ≠ 0) (e : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M : FullLattice 𝒪 K)
    (m : ↥M.1) (hm' : algebraMap 𝒪 K π • (m : Fin 2 → K) ∈ (FullLattice.act (scalarGL (piUnit π hπ)) M).1)
    (hmem : (1 : B) ⊗ₜ[𝒪] (⟨_, hm'⟩ : ↥(FullLattice.act (scalarGL (piUnit π hπ)) M).1) ∈
      e.line (FullLattice.act (scalarGL (piUnit π hπ)) M) ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act (scalarGL (piUnit π hπ)) M)))) :
    (1 : B) ⊗ₜ[𝒪] m ∈ e.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  set A := actBaseChange B (scalarGL (piUnit π hπ)) M with hA
  have hAm : A ((1 : B) ⊗ₜ[𝒪] m) = (1 : B) ⊗ₜ[𝒪] (⟨_, hm'⟩ : ↥(FullLattice.act (scalarGL (piUnit π hπ)) M).1) := by
    rw [hA, actBaseChange_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
    rfl
  rw [← hAm, e.homothety (piUnit π hπ) M] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hz' : A.symm z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
    refine Submodule.smul_induction_on (p := fun z => A.symm z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) hz
      (fun r hr n _ => ?_) (fun a b ha hb => ?_)
    · show A.symm (r • n) ∈ _
      rw [LinearEquiv.map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · show A.symm (a + b) ∈ _
      rw [LinearEquiv.map_add]; exact Submodule.add_mem _ ha hb
  have h1m : (1 : B) ⊗ₜ[𝒪] m = y₀ + A.symm z := by
    apply A.injective
    rw [map_add, LinearEquiv.apply_symm_apply, ← hyz]
    rfl
  rw [h1m]
  exact Submodule.mem_sup.mpr ⟨y₀, hy₀, A.symm z, hz', rfl⟩

theorem edgeNondegAt_swap (hπ : algebraMap 𝒪 K π ≠ 0) (e : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K)
    (he : e.EdgeNondegAt π 𝔭 M' M) : e.EdgeNondegAt π 𝔭 (FullLattice.act (scalarGL (piUnit π hπ)) M) M' := by
  obtain ⟨hle, hπM, h1, h2⟩ := he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, rfl⟩ := (mem_act_pi_iff π hπ M v).mp hv
    exact hπM w
  · intro v
    exact (mem_act_pi_iff π hπ M _).mpr ⟨⟨v, hle v.2⟩, rfl⟩
  ·
    intro v hv
    apply h2 v
    rintro ⟨w, hw⟩
    exact hv ((mem_act_pi_iff π hπ M _).mpr ⟨w, hw⟩)
  ·
    intro v' hv' hmem
    obtain ⟨m, hm⟩ := (mem_act_pi_iff π hπ M _).mp v'.2
    have hmM' : (m : Fin 2 → K) ∉ M'.1 := by
      intro hmM'
      exact hv' ⟨⟨m, hmM'⟩, hm⟩
    apply h1 m hmM'
    have hv'eq : v' = ⟨algebraMap 𝒪 K π • (m : Fin 2 → K), hm ▸ v'.2⟩ := Subtype.ext hm
    rw [hv'eq] at hmem
    exact tmul_mem_of_tmul_smul_mem π hπ e 𝔭 M m _ hmem

end Swap

theorem scalarGL_c₀ {c₀ c₁ : Kˣ} (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁) (hπ : algebraMap 𝒪 K π ≠ 0) (g : GL (Fin 2) K) :
    scalarGL c₀ * g⁻¹ = scalarGL (piUnit π hπ) * (scalarGL c₁ * g⁻¹) := by
  have hc' : c₀ = piUnit π hπ * c₁ := Units.ext (by rw [Units.val_mul]; exact hc)
  rw [hc', scalarGL_mul, mul_assoc]

end P2mKcQuadrupleOdd

end

open P2mKcQuadrupleOdd in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g : GL (Fin 2) K) (c₀ c₁ : Kˣ)
    {Q Q' : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (ht : Q.IsTranslateOdd g c₀ c₁ Q') :
    Q'.IsQuadrupleOf (DeligneDatum.pullback π B g d) := by
  obtain ⟨t⟩ := ht
  have hπ : algebraMap 𝒪 K π ≠ 0 := by
    intro h0
    apply c₀.ne_zero
    rw [t.c₀_eq, h0, zero_mul]
  have hγh₁ : (g * (scalarGL c₁)⁻¹) * (scalarGL c₁ * g⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (scalarGL c₁)⁻¹, inv_mul_cancel, one_mul, mul_inv_cancel]
  have hγh₀ : (g * (scalarGL c₀)⁻¹) * (scalarGL c₀ * g⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (scalarGL c₀)⁻¹, inv_mul_cancel, one_mul, mul_inv_cancel]
  have hpull₁ : DeligneDatum.pullback π B (g * (scalarGL c₁)⁻¹) d = DeligneDatum.pullback π B g d := by
    rw [pullback_mul, scalarGL_inv, pullback_scalarGL]
  have hpull₀ : DeligneDatum.pullback π B (g * (scalarGL c₀)⁻¹) d = DeligneDatum.pullback π B g d := by
    rw [pullback_mul, scalarGL_inv, pullback_scalarGL]
  intro x
  obtain ⟨hedge, hk₀, hk₁⟩ := h x
  have hL₀ : Q'.L₀ x = FullLattice.act (scalarGL c₀ * g⁻¹) (Q.L₁ x) := Subtype.ext (t.N₀_eq x)
  have hL₁ : Q'.L₁ x = FullLattice.act (scalarGL c₁ * g⁻¹) (Q.L₀ x) := Subtype.ext (t.N₁_eq x)
  refine ⟨?_, ?_, ?_⟩
  ·
    have heven := edgeNondegAt_pullback π (g * (scalarGL c₁)⁻¹) (scalarGL c₁ * g⁻¹) hγh₁ d x.asIdeal _ _ hedge
    rw [hpull₁] at heven
    have hsw := edgeNondegAt_swap π hπ (DeligneDatum.pullback π B g d) x.asIdeal _ _ heven
    have hL₀' : Q'.L₀ x = FullLattice.act (scalarGL (piUnit π hπ)) (FullLattice.act (scalarGL c₁ * g⁻¹) (Q.L₁ x)) := by
      rw [hL₀]
      apply Subtype.ext
      show latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x) = latticeMap (scalarGL (piUnit π hπ)) (latticeMap (scalarGL c₁ * g⁻¹) (Q.N₁ x))
      rw [← latticeMap_mul, scalarGL_c₀ π t.c₀_eq hπ g]
    rw [hL₀', hL₁]
    exact hsw
  · have key := ker_transfer π (g * (scalarGL c₀)⁻¹) (scalarGL c₀ * g⁻¹) hγh₀ x (Q.L₁ x) (Q'.L₀ x) hL₀ t.σ₀ (Q.u₁ x) (Q'.u₀ x)
      (fun v hv hv' => t.σ₀_u₀ x v hv hv') d hk₁
    rwa [hpull₀] at key
  · have key := ker_transfer π (g * (scalarGL c₁)⁻¹) (scalarGL c₁ * g⁻¹) hγh₁ x (Q.L₀ x) (Q'.L₁ x) hL₁ t.σ₁ (Q.u₀ x) (Q'.u₁ x)
      (fun v hv hv' => t.σ₁_u₁ x v hv hv') d hk₀
    rwa [hpull₁] at key

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd (solution)
