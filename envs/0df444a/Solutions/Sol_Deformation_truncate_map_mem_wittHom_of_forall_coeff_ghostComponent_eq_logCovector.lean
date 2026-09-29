-- Prove2me | solution 1 for Deformation.truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c873b148-5824-547b-af72-8db235f10894

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
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_Deformation_map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector
import Theorems.Thm_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
import Theorems.Thm_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector

set_option autoImplicit false

universe u v

namespace S17L2c

open scoped TensorProduct
open MvPowerSeries

section Kappa

variable (𝓞 : Type*) [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] (R : Type*) [CommRing R] [HopfAlgebra 𝓞 R]

abbrev Ak := TensorProduct 𝓞 (ZMod p) R

abbrev Bk := (Ak 𝓞 p R) ⊗[ZMod p] (Ak 𝓞 p R)

noncomputable def incR : R →ₐ[𝓞] Ak 𝓞 p R := Algebra.TensorProduct.includeRight
noncomputable def iL : Ak 𝓞 p R →ₐ[ZMod p] Bk 𝓞 p R := Algebra.TensorProduct.includeLeft
noncomputable def iR : Ak 𝓞 p R →ₐ[ZMod p] Bk 𝓞 p R := Algebra.TensorProduct.includeRight

noncomputable def kap : R ⊗[𝓞] R →ₐ[𝓞] Bk 𝓞 p R :=
  Algebra.TensorProduct.lift (((iL 𝓞 p R).restrictScalars 𝓞).comp (incR 𝓞 p R))
    (((iR 𝓞 p R).restrictScalars 𝓞).comp (incR 𝓞 p R)) (fun x y => Commute.all (S := Bk 𝓞 p R) _ _)

theorem kap_tmul (u v : R) : kap 𝓞 p R (u ⊗ₜ v) = (incR 𝓞 p R u) ⊗ₜ (incR 𝓞 p R v) := by
  rw [kap, Algebra.TensorProduct.lift_tmul]
  simp [iL, iR, Algebra.TensorProduct.tmul_mul_tmul]

set_option synthInstance.maxHeartbeats 400000 in
theorem ttt_apply (t : R ⊗[𝓞] R) :
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm 𝓞 (ZMod p) 𝓞 (ZMod p) (ZMod p) (ZMod p) R R
      (((1 : ZMod p) ⊗ₜ[ZMod p] (1 : ZMod p)) ⊗ₜ[𝓞] t) = kap 𝓞 p R t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | tmul u v =>
    rw [kap_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

set_option synthInstance.maxHeartbeats 400000 in

theorem comul_incR (r : R) : Coalgebra.comul (R := ZMod p) (incR 𝓞 p R r) = kap 𝓞 p R (Coalgebra.comul (R := 𝓞) r) := by
  rw [incR, Algebra.TensorProduct.includeRight_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply, ttt_apply]

theorem kap_includeLeft (r : R) :
    kap 𝓞 p R ((Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) r) = iL 𝓞 p R (incR 𝓞 p R r) := by
  rw [Algebra.TensorProduct.includeLeft_apply, kap_tmul, map_one]; rfl

theorem kap_includeRight (r : R) :
    kap 𝓞 p R ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) r) = iR 𝓞 p R (incR 𝓞 p R r) := by
  rw [Algebra.TensorProduct.includeRight_apply, kap_tmul, map_one]; rfl

theorem p_eq_zero_B : (p : Bk 𝓞 p R) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (Bk 𝓞 p R)), ZMod.natCast_self, map_zero]

theorem p_eq_zero_A : (p : Ak 𝓞 p R) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (Ak 𝓞 p R)), ZMod.natCast_self, map_zero]

theorem incR_eq_zero_of_mem {x : R} (hx : x ∈ Ideal.span {(p : R)}) : incR 𝓞 p R x = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast, p_eq_zero_A, mul_zero]

end Kappa

section Generic

variable {p : ℕ} [Fact p.Prime]

theorem witt_map_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : WittVector p R) : WittVector.map g (WittVector.map f x) = WittVector.map (g.comp f) x := by
  ext n; simp [WittVector.map_coeff]

theorem window {B : Type*} [CommRing B] (r N : ℕ) (x y z : WittVector p B)
    (hx : ∀ j < r, x.coeff j = 0) (hy : ∀ j < r, y.coeff j = 0) (hz : ∀ j < r, z.coeff j = 0)
    (hw : ∀ j, r ≤ j → j < r + N → (x - y - z).coeff j = 0) :
    WittVector.truncate N (x.shift r) = WittVector.truncate N (y.shift r) + WittVector.truncate N (z.shift r) := by
  have ex := WittVector.eq_iterate_verschiebung hx
  have ey := WittVector.eq_iterate_verschiebung hy
  have ez := WittVector.eq_iterate_verschiebung hz
  set w := x.shift r - y.shift r - z.shift r with hwdef
  have key : x - y - z = (WittVector.verschiebung^[r]) w := by
    rw [hwdef, iterate_map_sub (WittVector.verschiebung : WittVector p B →+ WittVector p B),
      iterate_map_sub (WittVector.verschiebung : WittVector p B →+ WittVector p B), ← ex, ← ey, ← ez]
  have hcoef : ∀ j < N, w.coeff j = 0 := by
    intro j hj
    rw [← WittVector.iterate_verschiebung_coeff w r j, ← key]
    exact hw (j + r) (by omega) (by omega)
  have ht : WittVector.truncate N w = 0 := RingHom.mem_ker.1 ((WittVector.mem_ker_truncate N w).2 hcoef)
  rw [hwdef, map_sub, map_sub] at ht
  linear_combination ht

theorem apply_eq_zero_of_mem {𝓞 : Type*} [CommRing 𝓞] {σ : Type*} {C : Type*} [CommRing C]
    (τ : MvPowerSeries σ 𝓞 →+* C) (hp0 : τ (p : MvPowerSeries σ 𝓞) = 0) {E : ℕ}
    (hE : (Ideal.span (Set.range fun s => τ (X s))) ^ E = ⊥) {x : MvPowerSeries σ 𝓞}
    (hx : x ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} ⊔ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E) :
    τ x = 0 := by
  have hmap : Ideal.map τ (Ideal.span {(p : MvPowerSeries σ 𝓞)} ⊔
      (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E) = ⊥ := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton, hp0,
      Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq, ← Set.range_comp]
    exact hE
  have := Ideal.mem_map_of_mem τ hx
  rwa [hmap, Ideal.mem_bot] at this

theorem exists_span_pow_eq_bot {C : Type*} [CommRing C] {ι : Type*} [Finite ι] (t : ι → C) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ E, (Ideal.span (Set.range t)) ^ E = ⊥ := by
  have hfg : (Ideal.span (Set.range t)).FG := ⟨(Set.finite_range t).toFinset, by simp⟩
  have hle : Ideal.span (Set.range t) ≤ nilradical C := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  obtain ⟨E, hE⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  exact ⟨E, hE⟩

theorem pow_eq_bot_of_le {C : Type*} [CommRing C] {I : Ideal C} {E E' : ℕ} (hE : I ^ E = ⊥) (h : E ≤ E') : I ^ E' = ⊥ :=
  le_bot_iff.1 ((Ideal.pow_le_pow_right h).trans hE.le)

theorem tmul_one_mem_radical {𝓞 : Type*} [CommRing 𝓞] {R : Type*} [CommRing R] [Algebra 𝓞 R] {a : R}
    (ha : a ∈ (Ideal.span {(p : R)}).radical) : a ⊗ₜ[𝓞] (1 : R) ∈ (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 he
  refine ⟨e, Ideal.mem_span_singleton'.2 ⟨t ⊗ₜ 1, ?_⟩⟩
  have hp' : (p : R ⊗[𝓞] R) = (p : R) ⊗ₜ[𝓞] (1 : R) := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R), Algebra.TensorProduct.includeLeft_apply]
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← ht, hp', Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem one_tmul_mem_radical {𝓞 : Type*} [CommRing 𝓞] {R : Type*} [CommRing R] [Algebra 𝓞 R] {a : R}
    (ha : a ∈ (Ideal.span {(p : R)}).radical) : (1 : R) ⊗ₜ[𝓞] a ∈ (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 he
  refine ⟨e, Ideal.mem_span_singleton'.2 ⟨1 ⊗ₜ t, ?_⟩⟩
  have hp' : (p : R ⊗[𝓞] R) = (1 : R) ⊗ₜ[𝓞] (p : R) := by
    rw [← map_natCast (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R), Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← ht, hp', Algebra.TensorProduct.tmul_mul_tmul, mul_one]

end Generic

section Maps

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] {d : ℕ} (F : MvFormalGroup d 𝓞)
  (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R]
  [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)

noncomputable def wfam : Fin d ⊕ Fin d → R ⊗[𝓞] R :=
  Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j))

include hπX in
theorem wfam_mem (u : Fin d ⊕ Fin d) : wfam R π u ∈ (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
  rcases u with j | j
  · exact tmul_one_mem_radical (hπX j)
  · exact one_tmul_mem_radical (hπX j)

noncomputable def θ₀ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] R ⊗[𝓞] R :=
  MvFormalGroup.adicEvalAlgHom (Ideal.span {(p : R ⊗[𝓞] R)}) (wfam_mem p R π hπX)

theorem θ₀_apply (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    θ₀ p R π hπX G = MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)}) (wfam R π) G := by
  rw [θ₀, MvFormalGroup.coe_adicEvalAlgHom]

noncomputable def sF : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)
noncomputable def s₁ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))
noncomputable def s₂ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))

omit [Algebra 𝓞 (ZMod p)] in
theorem sF_X (s : Fin d) : sF F (X s) = F.toPowerSeries s := MvPowerSeries.substAlgHom_X _ s
omit [Algebra 𝓞 (ZMod p)] in
theorem s₁_X (s : Fin d) : s₁ (𝓞 := 𝓞) (d := d) (X s) = X (Sum.inl s) := MvPowerSeries.substAlgHom_X _ s
omit [Algebra 𝓞 (ZMod p)] in
theorem s₂_X (s : Fin d) : s₂ (𝓞 := 𝓞) (d := d) (X s) = X (Sum.inr s) := MvPowerSeries.substAlgHom_X _ s

include hπX in
theorem adicEval_F_mem (s : Fin d) :
    MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)}) (wfam R π) (F.toPowerSeries s) ∈ (Ideal.span {(p : R ⊗[𝓞] R)}).radical :=
  MvFormalGroup.adicEval_mem_radical _ (wfam_mem p R π hπX) (F.constantCoeff_eq_zero s)

variable (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))

include hπΔ in

theorem θ₀_sF (f : MvPowerSeries (Fin d) 𝓞) : θ₀ p R π hπX (sF F f) = Coalgebra.comul (R := 𝓞) (π f) := by
  have hfam : (fun s => (θ₀ p R π hπX).comp (sF F) (X s)) = fun s => ((Bialgebra.comulAlgHom 𝓞 R).comp π) (X s) := by
    funext s
    rw [AlgHom.comp_apply, AlgHom.comp_apply, sF_X, θ₀_apply, Bialgebra.comulAlgHom_apply, hπΔ]
    rfl
  have u1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((θ₀ p R π hπX).comp (sF F)) (fun s => by rw [AlgHom.comp_apply, sF_X, θ₀_apply]; exact adicEval_F_mem p F R π hπX s) f
  have u2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((Bialgebra.comulAlgHom 𝓞 R).comp π) (fun s => by
      rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, hπΔ]; exact adicEval_F_mem p F R π hπX s) f
  rw [hfam] at u1
  rw [AlgHom.comp_apply] at u1 u2
  rw [Bialgebra.comulAlgHom_apply] at u2
  rw [u1, u2]

theorem θ₀_s₁ (f : MvPowerSeries (Fin d) 𝓞) :
    θ₀ p R π hπX (s₁ f) = (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) (π f) := by
  have hfam : (fun s => (θ₀ p R π hπX).comp s₁ (X s)) =
      fun s => ((Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R).comp π) (X s) := by
    funext s
    rw [AlgHom.comp_apply, AlgHom.comp_apply, s₁_X, θ₀_apply, MvFormalGroup.adicEval_X,
      Algebra.TensorProduct.includeLeft_apply]
    rfl
  have u1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((θ₀ p R π hπX).comp s₁) (fun s => by
      rw [AlgHom.comp_apply, s₁_X, θ₀_apply, MvFormalGroup.adicEval_X]; exact wfam_mem p R π hπX _) f
  have u2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R).comp π) (fun s => by
      rw [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; exact wfam_mem p R π hπX (Sum.inl s)) f
  rw [hfam] at u1
  rw [AlgHom.comp_apply] at u1 u2
  rw [u1, u2]

theorem θ₀_s₂ (f : MvPowerSeries (Fin d) 𝓞) :
    θ₀ p R π hπX (s₂ f) = (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) (π f) := by
  have hfam : (fun s => (θ₀ p R π hπX).comp s₂ (X s)) =
      fun s => ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R).comp π) (X s) := by
    funext s
    rw [AlgHom.comp_apply, AlgHom.comp_apply, s₂_X, θ₀_apply, MvFormalGroup.adicEval_X,
      Algebra.TensorProduct.includeRight_apply]
    rfl
  have u1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((θ₀ p R π hπX).comp s₂) (fun s => by
      rw [AlgHom.comp_apply, s₂_X, θ₀_apply, MvFormalGroup.adicEval_X]; exact wfam_mem p R π hπX _) f
  have u2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : R ⊗[𝓞] R)})
    ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R).comp π) (fun s => by
      rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]; exact wfam_mem p R π hπX (Sum.inr s)) f
  rw [hfam] at u1
  rw [AlgHom.comp_apply] at u1 u2
  rw [u1, u2]

noncomputable def θ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →+* Bk 𝓞 p R := (kap 𝓞 p R).toRingHom.comp (θ₀ p R π hπX).toRingHom
noncomputable def θ₁ : MvPowerSeries (Fin d) 𝓞 →+* Ak 𝓞 p R :=
  (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp π.toRingHom

theorem θ_apply (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) : θ p R π hπX G = kap 𝓞 p R (θ₀ p R π hπX G) := rfl
theorem θ₁_apply (f : MvPowerSeries (Fin d) 𝓞) : θ₁ p R π f = incR 𝓞 p R (π f) := rfl

noncomputable def gOf (g : Ak 𝓞 p R →+* Bk 𝓞 p R) : MvPowerSeries (Fin d) 𝓞 →+* Bk 𝓞 p R := g.comp (θ₁ p R π)

theorem gOf_apply (g : Ak 𝓞 p R →+* Bk 𝓞 p R) (f : MvPowerSeries (Fin d) 𝓞) : gOf p R π g f = g (θ₁ p R π f) := rfl

noncomputable def wmap {T : Type*} [CommRing T] (g : T →+* Bk 𝓞 p R) (x : WittVector p T) : WittVector p (Bk 𝓞 p R) :=
  @WittVector.map p T (Bk 𝓞 p R) _ (inferInstance) _ g x

theorem wmap_coeff {T : Type*} [CommRing T] (g : T →+* Bk 𝓞 p R) (x : WittVector p T) (n : ℕ) :
    (wmap p R g x).coeff n = g (x.coeff n) := WittVector.map_coeff _ _ _

theorem wmap_sub {T : Type*} [CommRing T] (g : T →+* Bk 𝓞 p R) (x y : WittVector p T) :
    wmap p R g (x - y) = wmap p R g x - wmap p R g y := by unfold wmap; rw [map_sub]

theorem wmap_wittMap {T U : Type*} [CommRing T] [CommRing U] (f : T →+* U) (g : U →+* Bk 𝓞 p R) (x : WittVector p T) :
    wmap p R g (WittVector.map f x) = wmap p R (g.comp f) x := by
  ext n; simp [wmap, WittVector.map_coeff]

include hπΔ in
theorem θ_comp_sF : (θ p R π hπX).comp (sF F).toRingHom = gOf p R π (Deformation.comulRingHom (ZMod p) (Ak 𝓞 p R)) := by
  refine RingHom.ext fun f => ?_
  rw [RingHom.comp_apply, gOf_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, θ_apply, θ₀_sF p F R π hπX hπΔ,
    θ₁_apply, Deformation.comulRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Bialgebra.comulAlgHom_apply, comul_incR]

theorem θ_comp_s₁ : (θ p R π hπX).comp (s₁).toRingHom = gOf p R π (iL 𝓞 p R).toRingHom := by
  refine RingHom.ext fun f => ?_
  rw [RingHom.comp_apply, gOf_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, θ_apply, θ₀_s₁,
    θ₁_apply, kap_includeLeft, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

theorem θ_comp_s₂ : (θ p R π hπX).comp (s₂).toRingHom = gOf p R π (iR 𝓞 p R).toRingHom := by
  refine RingHom.ext fun f => ?_
  rw [RingHom.comp_apply, gOf_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, θ_apply, θ₀_s₂,
    θ₁_apply, kap_includeRight, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

include hπX in

theorem exists_common_exp : ∃ e : ℕ, ∀ j : Fin d, π (X j) ^ e ∈ Ideal.span {(p : R)} := by
  classical
  have h' : ∀ j : Fin d, ∃ n : ℕ, π (X j) ^ n ∈ Ideal.span {(p : R)} := fun j => hπX j
  choose e he using h'
  refine ⟨Finset.univ.sup e, fun j => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, Finset.univ.sup e = e j + t :=
    ⟨_, (Nat.add_sub_cancel' (Finset.le_sup (f := e) (Finset.mem_univ j))).symm⟩
  rw [ht, pow_add]
  exact Ideal.mul_mem_right _ _ (he j)

theorem θ₁_X_pow_eq_zero {e : ℕ} (he : ∀ j : Fin d, π (X j) ^ e ∈ Ideal.span {(p : R)}) (j : Fin d) :
    θ₁ p R π (X j ^ e) = 0 := by
  rw [θ₁_apply, map_pow]
  exact incR_eq_zero_of_mem 𝓞 p R (he j)

theorem θ_X_pow_eq_zero {e : ℕ} (he : ∀ j : Fin d, π (X j) ^ e ∈ Ideal.span {(p : R)}) (u : Fin d ⊕ Fin d) :
    θ p R π hπX (X u ^ e) = 0 := by
  rw [θ_apply, map_pow, θ₀_apply, MvFormalGroup.adicEval_X]
  rcases u with j | j
  · show kap 𝓞 p R ((π (X j) ⊗ₜ[𝓞] (1 : R)) ^ e) = 0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, kap_tmul, incR_eq_zero_of_mem 𝓞 p R (he j), TensorProduct.zero_tmul]
  · show kap 𝓞 p R (((1 : R) ⊗ₜ[𝓞] π (X j)) ^ e) = 0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, kap_tmul, incR_eq_zero_of_mem 𝓞 p R (he j), TensorProduct.tmul_zero]

theorem θ_p : θ p R π hπX (p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) = 0 := by rw [map_natCast, p_eq_zero_B]
theorem θ₁_p : θ₁ p R π (p : MvPowerSeries (Fin d) 𝓞) = 0 := by rw [map_natCast, p_eq_zero_A]

end Maps

section Kill

open scoped Pointwise

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*} [Fintype σ] {C : Type*} [NonAssocSemiring C]

theorem apply_eq_zero_of_mem_sup_pow (p : ℕ) (τ : MvPowerSeries σ 𝓞 →+* C) (hp0 : τ (p : MvPowerSeries σ 𝓞) = 0)
    (e : ℕ) (hnil : ∀ s : σ, τ (X s ^ (e + 1)) = 0) {E : ℕ} (hE : Fintype.card σ * e + 1 ≤ E)
    {r : MvPowerSeries σ 𝓞}
    (hr : r ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} ⊔ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E) :
    τ r = 0 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
  have hτa : τ a = 0 := by
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hp0, mul_zero]

  set E₀ := Fintype.card σ * e + 1 with hE₀
  have hb' : b ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E₀ := Ideal.pow_le_pow_right hE hb
  have hspan : (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E₀ =
      Ideal.span ((Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ E₀ : Set (MvPowerSeries σ 𝓞)) := Submodule.span_pow _ _
  rw [hspan] at hb'

  have hcore : ∀ x ∈ ((Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ E₀ : Set (MvPowerSeries σ 𝓞)), τ x = 0 := by
    intro x hx
    obtain ⟨f, hf⟩ := Set.mem_pow.1 hx
    have hu : ∀ i : Fin E₀, ∃ s : σ, X s = (f i : MvPowerSeries σ 𝓞) := fun i => (f i).2
    choose u hu using hu
    have hx' : x = ∏ i : Fin E₀, (X (u i) : MvPowerSeries σ 𝓞) := by
      rw [← hf, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (hu i).symm
    obtain ⟨s₀, hs₀⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card u (by rw [Fintype.card_fin, hE₀]; exact Nat.lt_succ_self _)
    rw [hx', ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => u i = s₀)]
    have hfib : ∏ i ∈ Finset.univ.filter (fun i => u i = s₀), (X (u i) : MvPowerSeries σ 𝓞) =
        X s₀ ^ (Finset.univ.filter (fun i => u i = s₀)).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
    rw [hfib]
    obtain ⟨t, ht⟩ : ∃ t, (Finset.univ.filter (fun i => u i = s₀)).card = (e + 1) + t :=
      ⟨(Finset.univ.filter (fun i => u i = s₀)).card - (e + 1), by omega⟩
    rw [ht, pow_add, mul_assoc, map_mul, hnil s₀, zero_mul]
  have hτb : τ b = 0 := by
    refine Submodule.span_induction (p := fun x _ => τ x = 0) hcore (map_zero τ) (fun x y _ _ hx hy => ?_)
      (fun c x _ hx => ?_) hb'
    · show τ (x + y) = 0
      rw [map_add, hx, hy, add_zero]
    · show τ (c • x) = 0
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  rw [map_add, hτa, hτb, add_zero]

end Kill

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
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (c : (Fin d →₀ ℕ) → 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
            (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
        ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
          (∀ n : ℕ, n < N → ∀ m' : Fin d →₀ ℕ,
            (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (N - 1 - n) • m')) →
          WittVector.truncate N (WittVector.map
              ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
                π.toRingHom) ℓ) ∈
            Deformation.wittHom (ZMod p) p N (TensorProduct 𝓞 (ZMod p) R) := by
  classical

  obtain ⟨e₀, he₀⟩ := exists_common_exp p R π hπX
  have he₁ : ∀ j : Fin d, π (X j) ^ (e₀ + 1) ∈ Ideal.span {(p : R)} := fun j => by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ (he₀ j)
  set E := Fintype.card (Fin d ⊕ Fin d) * e₀ + 1 with hEdef
  have hEA : Fintype.card (Fin d) * e₀ + 1 ≤ E := by
    rw [hEdef, Fintype.card_sum]; nlinarith
  have killB : ∀ {x : MvPowerSeries (Fin d ⊕ Fin d) 𝓞},
      x ∈ Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} ⊔
        (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E → θ p R π hπX x = 0 :=
    fun hx => apply_eq_zero_of_mem_sup_pow p (θ p R π hπX) (θ_p p R π hπX) e₀ (θ_X_pow_eq_zero p R π hπX he₁) le_rfl hx
  have killA : ∀ {x : MvPowerSeries (Fin d) 𝓞},
      x ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E → θ₁ p R π x = 0 :=
    fun hx => apply_eq_zero_of_mem_sup_pow p (θ₁ p R π) (θ₁_p p R π) e₀ (θ₁_X_pow_eq_zero p R π he₁) hEA hx

  have hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)} := fun c => by
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]
  have hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), ((m j + 1 : ℕ) : 𝓞) * MvPowerSeries.coeff (m + Finsupp.single j 1) (φ i) ∈
      Ideal.span {(p : 𝓞) ^ m.degree} := fun i j m =>
    MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m

  obtain ⟨n₀, hn₀⟩ := Deformation.map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector p hp hker F Fp hFp hFp0 φ
    hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip
  have factA := fun i => MvFormalGroup.coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le p hp hker F Fp
    hFp hFp0 φ hφ0 hφ1 hφT hφF i E n₀
  choose N₁ hN₁ using factA
  refine ⟨max n₀ (Finset.univ.sup N₁), fun N hN i c hc ℓ hℓ => ?_⟩
  have hNn₀ : n₀ ≤ N := (le_max_left _ _).trans hN
  have hN₁i : N₁ i ≤ N := ((Finset.le_sup (f := N₁) (Finset.mem_univ i)).trans (le_max_right _ _)).trans hN
  obtain ⟨M₀, hM₀⟩ := MvFormalGroup.coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector p hp hker F Fp
    hFp hFp0 φ hφ0 hφ1 hφT hφF i N E
  set M := max M₀ N with hM
  have hMN : N ≤ M := le_max_right _ _

  set cM : (Fin d →₀ ℕ) → 𝓞 := fun m => if m.degree ≤ M then (p : 𝓞) ^ (M - m.degree) * MvPowerSeries.coeff m (φ i)
    else if h : (p : 𝓞) ^ (m.degree - M) ∣ MvPowerSeries.coeff m (φ i) then Classical.choose h else 0 with hcM
  have hcMspec : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → cM m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
      (M < m.degree → cM m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
        (cM m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m)) := by
    intro m
    constructor
    · intro h; rw [hcM]; dsimp only; rw [if_pos h]
    · intro h
      have hn : ¬ m.degree ≤ M := not_le.2 h
      by_cases hd : (p : 𝓞) ^ (m.degree - M) ∣ MvPowerSeries.coeff m (φ i)
      · left; rw [hcM]; dsimp only; rw [if_neg hn, dif_pos hd, mul_comm]; exact (Classical.choose_spec hd).symm
      · right; refine ⟨?_, hd⟩; rw [hcM]; dsimp only; rw [if_neg hn, dif_neg hd]
  obtain ⟨ℓM, hℓM⟩ := MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_logCovector p hp hfrob (φ i) (hint i) M cM hcMspec
  set r := M - N with hr

  have hC1N : ∀ j, j < N - n₀ → θ₁ p R π (ℓ.coeff j) = 0 := by
    intro j hj
    have := hn₀ N i c hc ℓ hℓ (N - 1 - j) (by omega) (by omega)
    rw [show N - 1 - (N - 1 - j) = j by omega] at this
    rw [θ₁_apply, incR_eq_zero_of_mem 𝓞 p R this]
  have hC1M : ∀ j, j < M - n₀ → θ₁ p R π (ℓM.coeff j) = 0 := by
    intro j hj
    have := hn₀ M i cM hcMspec ℓM hℓM (M - 1 - j) (by omega) (by omega)
    rw [show M - 1 - (M - 1 - j) = j by omega] at this
    rw [θ₁_apply, incR_eq_zero_of_mem 𝓞 p R this]

  have hcmp : ∀ j, j < N → θ₁ p R π (ℓ.coeff j) = θ₁ p R π (ℓM.coeff (r + j)) := by
    intro j hj
    rcases Nat.lt_or_ge j (N - n₀) with hlo | hhi
    · rw [hC1N j hlo, hC1M (r + j) (by omega)]
    · have := hN₁ i N M hN₁i hMN c cM hc hcMspec ℓ ℓM hℓ hℓM j hhi hj
      have h0 := killA this
      rw [map_sub, sub_eq_zero] at h0
      rw [← h0, add_comm]

  have hDwin : ∀ j, M - N ≤ j → j < M → θ p R π hπX ((WittVector.map (sF F).toRingHom ℓM - WittVector.map (s₁).toRingHom ℓM -
      WittVector.map (s₂).toRingHom ℓM).coeff j) = 0 := fun j h1 h2 =>
    killB (hM₀ M (le_max_left _ _) cM hcMspec ℓM hℓM j h1 h2)
  have hmapD : wmap p R (θ p R π hπX) (WittVector.map (sF F).toRingHom ℓM - WittVector.map (s₁).toRingHom ℓM -
      WittVector.map (s₂).toRingHom ℓM) =
      wmap p R (gOf p R π (Deformation.comulRingHom (ZMod p) (Ak 𝓞 p R))) ℓM -
        wmap p R (gOf p R π (iL 𝓞 p R).toRingHom) ℓM - wmap p R (gOf p R π (iR 𝓞 p R).toRingHom) ℓM := by
    rw [wmap_sub, wmap_sub, wmap_wittMap, wmap_wittMap, wmap_wittMap, θ_comp_sF p F R π hπX hπΔ, θ_comp_s₁, θ_comp_s₂]
  have hvan : ∀ (g : Ak 𝓞 p R →+* Bk 𝓞 p R) (j : ℕ), j < r → (wmap p R (gOf p R π g) ℓM).coeff j = 0 := by
    intro g j hj
    rw [wmap_coeff, gOf_apply, hC1M j (by omega), map_zero]
  have hwin := window r N _ _ _ (hvan (Deformation.comulRingHom (ZMod p) (Ak 𝓞 p R))) (hvan (iL 𝓞 p R).toRingHom)
    (hvan (iR 𝓞 p R).toRingHom) (fun j h1 h2 => by
      rw [← hmapD, wmap_coeff]; exact hDwin j (by omega) (by omega))

  have hshift : ∀ (g : Ak 𝓞 p R →+* Bk 𝓞 p R),
      WittVector.truncate N (wmap p R (gOf p R π g) ℓ) = WittVector.truncate N ((wmap p R (gOf p R π g) ℓM).shift r) := by
    intro g
    ext k
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.shift_coeff, wmap_coeff, wmap_coeff,
      gOf_apply, gOf_apply, hcmp k k.isLt]
  have key : WittVector.truncate N (wmap p R (gOf p R π (Deformation.comulRingHom (ZMod p) (Ak 𝓞 p R))) ℓ) =
      WittVector.truncate N (wmap p R (gOf p R π (iL 𝓞 p R).toRingHom) ℓ) +
        WittVector.truncate N (wmap p R (gOf p R π (iR 𝓞 p R).toRingHom) ℓ) := by
    rw [hshift, hshift, hshift]; exact hwin

  rw [Deformation.mem_wittHom_iff, Deformation.TruncWitt.map_truncate, Deformation.TruncWitt.map_truncate,
    Deformation.TruncWitt.map_truncate, witt_map_map, witt_map_map, witt_map_map]
  exact key

end S17L2c

open scoped TensorProduct
open MvPowerSeries

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
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (c : (Fin d →₀ ℕ) → 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
            (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
        ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
          (∀ n : ℕ, n < N → ∀ m' : Fin d →₀ ℕ,
            (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (N - 1 - n) • m')) →
          WittVector.truncate N (WittVector.map
              ((Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom.comp
                π.toRingHom) ℓ) ∈
            Deformation.wittHom (ZMod p) p N (TensorProduct 𝓞 (ZMod p) R) :=
  S17L2c.main p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip

end S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector
end P2MW
export P2MW.S_Deformation_truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector (solution)
