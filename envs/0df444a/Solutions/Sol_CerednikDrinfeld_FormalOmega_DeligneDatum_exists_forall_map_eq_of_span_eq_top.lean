-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_forall_map_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bbd0efcc-fab5-5501-bc38-4fa29619b1be

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open TensorProduct LT.LatticeTree CerednikDrinfeld.FormalOmega

namespace OmegaGlueSol

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section BC
variable (L : Type) [CommRing L] [Algebra B L] [Algebra 𝒪 L] [IsScalarTower 𝒪 B L]

noncomputable def bcMap (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K L M :=
  AlgebraTensorModule.map (Algebra.linearMap B L) LinearMap.id

theorem bcMap_tmul (M : FullLattice 𝒪 K) (b : B) (v : ↥M.1) :
    bcMap L M (b ⊗ₜ[𝒪] v) = algebraMap B L b ⊗ₜ[𝒪] v := by
  simp [bcMap]

theorem bcMap_eq_rTensor (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    bcMap L M x = LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 B L).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => rw [bcMap_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem isBaseChange_bcMap (M : FullLattice 𝒪 K) : IsBaseChange L (bcMap (𝒪 := 𝒪) (K := K) (B := B) L M) := by
  refine IsBaseChange.of_equiv (AlgebraTensorModule.cancelBaseChange 𝒪 B L L (↥M.1)) fun x => ?_
  rw [bcMap_eq_rTensor, cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B L) (fun _ => rfl) M x]

theorem isLocalizedModule_bcMap (S : Submonoid B) [IsLocalization S L] (M : FullLattice 𝒪 K) :
    IsLocalizedModule S (bcMap (𝒪 := 𝒪) (K := K) (B := B) L M) :=
  (isLocalizedModule_iff_isBaseChange S L _).mpr (isBaseChange_bcMap L M)

theorem lineBaseChange_eq_localized' (S : Submonoid B) [IsLocalization S L] (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) L S M
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 B L) M N = N.localized' L S (bcMap L M) := by
  haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) L S M
  rw [Submodule.localized'_eq_span, lineBaseChange]
  have himg : (LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 B L).toLinearMap) '' (N : Set (latticeBaseChange 𝒪 K B M)) =
      (bcMap (𝒪 := 𝒪) (K := K) L M) '' (N : Set (latticeBaseChange 𝒪 K B M)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, bcMap_eq_rTensor L M x⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (bcMap_eq_rTensor L M x).symm⟩
  rw [himg]

theorem lineBaseChange_congr {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {f g : B →ₐ[𝒪] B'} (h : ∀ b, f b = g b)
    (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange f M N = lineBaseChange g M N := by
  rw [AlgHom.ext h]

end BC

section Glue

variable {n : ℕ} (f : Fin n → B)
  (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
  [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
  (π : 𝒪) (x : ∀ i, OmegaObj (K := K) π (L i))

noncomputable def glueLine (M : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B M) :=
  ⨅ i, (((x i).line M).restrictScalars B).comap (bcMap (L i) M)

theorem mem_glueLine (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    y ∈ glueLine (B := B) L π x M ↔ ∀ i, bcMap (L i) M y ∈ (x i).line M := by
  simp [glueLine, Submodule.mem_iInf]

theorem bcMap_mem_of_mem_glueLine {M : FullLattice 𝒪 K} {y : latticeBaseChange 𝒪 K B M}
    (hy : y ∈ glueLine (B := B) L π x M) (i : Fin n) : bcMap (L i) M y ∈ (x i).line M :=
  (mem_glueLine L π x M y).mp hy i

theorem glueLine_mono {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) :
    (glueLine (B := B) L π x M').map (inclBaseChange B h) ≤ glueLine (B := B) L π x M := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_glueLine]
  intro i
  have h1 : bcMap (L i) M (inclBaseChange B h y) = inclBaseChange (L i) h (bcMap (L i) M' y) := by
    rw [bcMap_eq_rTensor, bcMap_eq_rTensor, rTensor_inclBaseChange]
  rw [h1]
  exact (x i).mono h (Submodule.mem_map_of_mem (bcMap_mem_of_mem_glueLine L π x hy i))

theorem glueLine_homothety (c : Kˣ) (M : FullLattice 𝒪 K) :
    glueLine (B := B) L π x (FullLattice.act (scalarGL c) M) =
      (glueLine (B := B) L π x M).map (actBaseChange B (scalarGL c) M).toLinearMap := by
  have nat : ∀ (i : Fin n) (z : latticeBaseChange 𝒪 K B M),
      bcMap (L i) (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M z) =
        actBaseChange (L i) (scalarGL c) M (bcMap (L i) M z) := by
    intro i z
    rw [bcMap_eq_rTensor, bcMap_eq_rTensor]
    exact rTensor_actBaseChange (IsScalarTower.toAlgHom 𝒪 B (L i)) (scalarGL c) M z
  ext y
  rw [mem_glueLine, Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨(actBaseChange B (scalarGL c) M).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [mem_glueLine]
    intro i
    have h1 := hy i
    rw [(x i).homothety c M] at h1
    have h2 := nat i ((actBaseChange B (scalarGL c) M).symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [h2] at h1
    obtain ⟨w', hw', he⟩ := h1
    have hw : w' = bcMap (L i) M ((actBaseChange B (scalarGL c) M).symm y) :=
      (actBaseChange (L i) (scalarGL c) M).injective he
    rw [← hw]
    exact hw'
  · rintro ⟨z, hz, rfl⟩ i
    show bcMap (L i) (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M z) ∈ _
    rw [nat i z, (x i).homothety c M]
    exact Submodule.mem_map_of_mem ((mem_glueLine L π x M z).mp hz i)

theorem one_tmul_mem_sup_of_mem_sup (𝔭 : Ideal B) (i : Fin n) (M : FullLattice 𝒪 K) (v : ↥M.1)
    (h : (1 : B) ⊗ₜ[𝒪] v ∈ glueLine (B := B) L π x M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    (1 : L i) ⊗ₜ[𝒪] v ∈ (x i).line M ⊔
      ((Ideal.map (algebraMap B (L i)) 𝔭) • ⊤ : Submodule (L i) (latticeBaseChange 𝒪 K (L i) M)) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  have himg : bcMap (L i) M ((1 : B) ⊗ₜ[𝒪] v) = (1 : L i) ⊗ₜ[𝒪] v := by rw [bcMap_tmul, map_one]
  rw [← himg, ← hyz, map_add]
  refine Submodule.add_mem_sup (bcMap_mem_of_mem_glueLine L π x hy i) ?_
  refine Submodule.smul_induction_on
    (p := fun w => bcMap (L i) M w ∈ ((Ideal.map (algebraMap B (L i)) 𝔭) • ⊤ : Submodule (L i) (latticeBaseChange 𝒪 K (L i) M)))
    hz (fun b hb w _ => ?_) (fun a a' ha ha' => ?_)
  · show bcMap (L i) M (b • w) ∈ _
    rw [LinearMap.map_smul, ← algebraMap_smul (L i) b]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) Submodule.mem_top
  · show bcMap (L i) M (a + a') ∈ _
    rw [map_add]
    exact Submodule.add_mem _ ha ha'

theorem glueLine_nondeg (hf : Ideal.span (Set.range f) = ⊤) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : B) ⊗ₜ[𝒪] v ∉ glueLine (B := B) L π x M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ glueLine (B := B) L π x M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) := by
  classical
  have hex : ∃ i, f i ∉ 𝔭 := by
    by_contra hall
    push_neg at hall
    have hle : Ideal.span (Set.range f) ≤ 𝔭 := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    rw [hf, top_le_iff] at hle
    exact h𝔭.ne_top hle
  obtain ⟨i, hi⟩ := hex
  have hdisj : Disjoint (↑(Submonoid.powers (f i)) : Set B) ↑𝔭 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hi (h𝔭.mem_of_pow_mem k hk)
  have h𝔮 : (Ideal.map (algebraMap B (L i)) 𝔭).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f i)) (L i) 𝔭 h𝔭 hdisj
  obtain ⟨M', M, hle, hπ, h1, h2⟩ := (x i).nondeg (Ideal.map (algebraMap B (L i)) 𝔭) h𝔮
  exact ⟨M', M, hle, hπ, fun v hv hmem => h1 v hv (one_tmul_mem_sup_of_mem_sup L π x 𝔭 i M v hmem),
    fun v' hv' hmem => h2 v' hv' (one_tmul_mem_sup_of_mem_sup L π x 𝔭 i M' v' hmem)⟩

end Glue

theorem isLocalization_away_of_away_mul {B : Type} [CommRing B] (S T : Type) [CommRing S] [CommRing T]
    [Algebra B S] [Algebra B T] [Algebra S T] [IsScalarTower B S T] (a b : B)
    [IsLocalization.Away b S] [IsLocalization.Away (a * b) T] :
    IsLocalization.Away (algebraMap B S a) T := by
  let T' := Localization.Away (algebraMap B S a)
  haveI : IsLocalization.Away (a * b) T' := inferInstance
  let e : T' ≃ₐ[B] T := IsLocalization.algEquiv (Submonoid.powers (a * b)) T' T
  have hcomp : ((e : T' →+* T).comp (algebraMap S T')).comp (algebraMap B S) = (algebraMap S T).comp (algebraMap B S) := by
    ext c
    show e (algebraMap S T' (algebraMap B S c)) = algebraMap S T (algebraMap B S c)
    rw [← IsScalarTower.algebraMap_apply B S T', AlgEquiv.commutes, IsScalarTower.algebraMap_apply B S T]
  have he : ∀ s : S, e (algebraMap S T' s) = algebraMap S T s := fun s =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) hcomp) s
  let e' : T' ≃ₐ[S] T := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) he
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap B S a)) e'

end OmegaGlueSol

open OmegaGlueSol in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
    [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (L₂ : Fin n → Fin n → Type) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra B (L₂ i j)] [∀ i j, Algebra 𝒪 (L₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (L₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (l : ∀ i j, L i →ₐ[𝒪] L₂ i j) (r : ∀ i j, L j →ₐ[𝒪] L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b)
    (x : ∀ i, OmegaObj (K := K) π (L i))
    (hx : ∀ i j, DeligneDatum.map π (l i j) (x i) = DeligneDatum.map π (r i j) (x j)) :
    ∃ d : OmegaObj (K := K) π B, ∀ i, DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d = x i := by
  classical

  have hcompat : ∀ (i j : Fin n) (M : FullLattice 𝒪 K),
      lineBaseChange (l i j) M ((x i).line M) = lineBaseChange (r i j) M ((x j).line M) :=
    fun i j M => congrArg (fun e : DeligneDatum (K := K) π (L₂ i j) => e.line M) (hx i j)

  have hfinM : ∀ M : FullLattice 𝒪 K, Module.Finite 𝒪 ↥M.1 := fun M => Module.Finite.iff_fg.mpr M.2.1

  have hA' : ∀ (M : FullLattice 𝒪 K) (z : latticeBaseChange 𝒪 K B M) (i : Fin n),
      bcMap (L i) M z ∈ (x i).line M → ∃ m : ℕ, (f i) ^ m • z ∈ glueLine (B := B) L π x M := by
    intro M z i hz
    have step : ∀ j : Fin n, ∃ m : ℕ, (algebraMap B (L j) (f i)) ^ m • bcMap (L j) M z ∈ (x j).line M := by
      intro j
      letI algj : Algebra (L j) (L₂ i j) := (r i j).toRingHom.toAlgebra
      haveI : IsScalarTower B (L j) (L₂ i j) := IsScalarTower.of_algebraMap_eq fun b => (hr i j b).symm
      haveI : IsScalarTower 𝒪 (L j) (L₂ i j) := IsScalarTower.of_algebraMap_eq fun a => ((r i j).commutes a).symm
      haveI : IsLocalization.Away (algebraMap B (L j) (f i)) (L₂ i j) :=
        isLocalization_away_of_away_mul (L j) (L₂ i j) (f i) (f j)
      haveI hlm := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j)
        (Submonoid.powers (algebraMap B (L j) (f i))) M

      have himg' : ∀ w : latticeBaseChange 𝒪 K B M, bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) M (bcMap (L j) M w) =
          LinearMap.rTensor (↥M.1) (l i j).toLinearMap (bcMap (L i) M w) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul b v =>
          rw [bcMap_tmul, bcMap_tmul, bcMap_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hl]
          show (r i j) (algebraMap B (L j) b) ⊗ₜ[𝒪] v = _
          rw [hr]
        | add a a' ha ha' => simp only [map_add, ha, ha']
      have himg := himg' z
      have hmem : bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) M (bcMap (L j) M z) ∈
          ((x j).line M).localized' (L₂ i j) (Submonoid.powers (algebraMap B (L j) (f i)))
            (bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) M) := by
        rw [← lineBaseChange_eq_localized' (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) (Submonoid.powers _) M ((x j).line M),
          lineBaseChange_congr (f := IsScalarTower.toAlgHom 𝒪 (L j) (L₂ i j)) (g := r i j) (fun b => rfl) M,
          ← hcompat i j M, himg]
        exact Submodule.subset_span ⟨_, hz, rfl⟩
      rw [Submodule.mem_localized'] at hmem
      obtain ⟨nn, hnn, t, ht⟩ := hmem
      rw [IsLocalizedModule.mk'_eq_iff] at ht

      have ht' : bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) M ((t : L j) • bcMap (L j) M z - nn) = 0 := by
        rw [map_sub, LinearMap.map_smul, ht, Submonoid.smul_def, sub_self]
      obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (algebraMap B (L j) (f i)))
        (bcMap (𝒪 := 𝒪) (K := K) (B := L j) (L₂ i j) M)).mp ht'
      obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).mp (c * t).2
      refine ⟨e, ?_⟩
      have hct : ((c * t : ↥(Submonoid.powers (algebraMap B (L j) (f i)))) : L j) • bcMap (L j) M z = (c : L j) • nn := by
        rw [Submonoid.smul_def, smul_sub, sub_eq_zero, smul_smul] at hc
        rw [Submonoid.coe_mul]
        exact hc
      rw [he, hct]
      exact Submodule.smul_mem _ _ hnn
    choose m hm using step
    refine ⟨Finset.univ.sup m, (mem_glueLine L π x M _).mpr fun j => ?_⟩
    rw [LinearMap.map_smul, ← algebraMap_smul (L j), map_pow]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hk, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hm j)

  have hA : ∀ (M : FullLattice 𝒪 K) (i : Fin n),
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (L i)) M (glueLine (B := B) L π x M) = (x i).line M := by
    intro M i
    haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (L i) (Submonoid.powers (f i)) M
    rw [lineBaseChange_eq_localized' (L i) (Submonoid.powers (f i)) M]
    apply le_antisymm
    · rw [Submodule.localized'_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨y, hy, rfl⟩
      exact bcMap_mem_of_mem_glueLine L π x hy i
    · intro y hy
      obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (bcMap (L i) M) y

      have hz : bcMap (L i) M z ∈ (x i).line M := by
        rw [← hzs, Submonoid.smul_def, ← algebraMap_smul (L i)]
        exact Submodule.smul_mem _ _ hy
      obtain ⟨m, hm⟩ := hA' M z i hz
      rw [Submodule.mem_localized']
      refine ⟨(f i) ^ m • z, hm, ⟨(f i) ^ m, m, rfl⟩ * s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff, LinearMap.map_smul, ← hzs, Submonoid.smul_def, Submonoid.smul_def,
        Submonoid.coe_mul, smul_smul]

  have hB : ∀ M : FullLattice 𝒪 K, Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ glueLine (B := B) L π x M) := by
    intro M

    have hInv : ∀ i, Module.Invertible (L i) (L i ⊗[B] (latticeBaseChange 𝒪 K B M ⧸ glueLine (B := B) L π x M)) := by
      intro i
      haveI := (x i).invertible M
      have hker : (x i).line M = LinearMap.ker (Module.Grassmannian.baseChangeMkQ (L i) (glueLine (B := B) L π x M)) := by
        rw [← lineBaseChange_eq_ker (IsScalarTower.toAlgHom 𝒪 B (L i)) (fun _ => rfl) M, hA M i]
      exact Module.Invertible.congr
        ((Submodule.quotEquivOfEq _ _ hker).trans (Module.Grassmannian.baseChangeMkQEquiv (B := L i) (glueLine (B := B) L π x M)))

    let Q := latticeBaseChange 𝒪 K B M ⧸ glueLine (B := B) L π x M
    let idx : ↥(Set.range f) → Fin n := fun g => g.2.choose
    have hidx : ∀ g : ↥(Set.range f), f (idx g) = (g : B) := fun g => g.2.choose_spec
    haveI instA : ∀ g : ↥(Set.range f), IsLocalization.Away (g : B) (L (idx g)) := fun g =>
      hidx g ▸ (inferInstance : IsLocalization.Away (f (idx g)) (L (idx g)))
    haveI instM : ∀ g : ↥(Set.range f), IsLocalizedModule (Submonoid.powers (g : B)) (TensorProduct.mk B (L (idx g)) Q 1) :=
      fun g => hidx g ▸ IsLocalization.tensorProduct_isLocalizedModule (Submonoid.powers (f (idx g))) (L (idx g))
    exact Module.Invertible.of_isLocalizedModule_of_span_eq_top (Set.range f) hf (Mₚ := fun g => L (idx g) ⊗[B] Q)
      (Rₚ := fun g => L (idx g)) (fun g => TensorProduct.mk B (L (idx g)) Q 1) (fun g => hInv (idx g))
  refine ⟨⟨fun M => glueLine (B := B) L π x M, hB, glueLine_mono L π x, glueLine_homothety L π x,
    glueLine_nondeg f L π x hf⟩, fun i => ?_⟩
  apply DeligneDatum.ext'
  funext M
  exact hA M i

#print axioms solution

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top (solution)
