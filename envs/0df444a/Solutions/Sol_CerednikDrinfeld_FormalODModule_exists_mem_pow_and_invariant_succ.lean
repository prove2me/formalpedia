-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_mem_pow_and_invariant_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1d6ed4ca-ca49-5287-b567-9d12a6d48a41

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero
import Theorems.Thm_HopfAlgebra_exists_eq_coaction_sub_tmul_one_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

namespace LiftStep

open MvPowerSeries MvFormalGroup

section Calculus

variable {B : Type} [CommRing B]

theorem mem_radical_bot_of_isNilpotent {S : Type} [CommRing S] {s : S} (h : IsNilpotent s) :
    s ∈ (⊥ : Ideal S).radical := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simp [hn]⟩

abbrev wpt {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    (a : Fin 2 → S) (b : Fin 2 → L) : Fin 2 ⊕ Fin 2 → S ⊗[B] L :=
  Sum.elim (fun j => a j ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] b j)

theorem wpt_nil {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ s, wpt a b s ∈ (⊥ : Ideal (S ⊗[B] L)).radical := by
  rintro (j | j)
  · obtain ⟨n, hn⟩ := ha j
    refine ⟨n, ?_⟩
    simp [wpt, Algebra.TensorProduct.tmul_pow, hn]
  · obtain ⟨n, hn⟩ := hb j
    refine ⟨n, ?_⟩
    simp [wpt, Algebra.TensorProduct.tmul_pow, hn]

noncomputable abbrev ptF (F : MvFormalGroup 2 B) {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    (a : Fin 2 → S) (b : Fin 2 → L) : Fin 2 → S ⊗[B] L :=
  fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) (F.toPowerSeries i)

theorem ptF_nil (F : MvFormalGroup 2 B) {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i, ptF F a b i ∈ (⊥ : Ideal (S ⊗[B] L)).radical :=
  fun i => MvFormalGroup.adicEval_mem_radical (⊥ : Ideal (S ⊗[B] L)) (wpt_nil ha hb) (F.constantCoeff_eq_zero i)

theorem map_comp_wpt {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') (a : Fin 2 → S) (b : Fin 2 → L) :
    (fun s => Algebra.TensorProduct.map φ (AlgHom.id B L) (wpt a b s)) = wpt (fun j => φ (a j)) b := by
  funext s
  rcases s with j | j <;> simp [wpt]

theorem map_adicEval_wpt {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) (G : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    Algebra.TensorProduct.map φ (AlgHom.id B L) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) G) =
      MvFormalGroup.adicEval (⊥ : Ideal (S' ⊗[B] L)) (wpt (fun j => φ (a j)) b) G := by
  rw [MvFormalGroup.map_adicEval (⊥ : Ideal (S ⊗[B] L)) (⊥ : Ideal (S' ⊗[B] L))
      (Algebra.TensorProduct.map φ (AlgHom.id B L)) Submodule.fg_bot
      (fun s hs => by rw [Ideal.mem_bot] at hs; simp [hs]) (wpt_nil ha hb), map_comp_wpt]

theorem map_ptF (F : MvFormalGroup 2 B) {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    (fun i => Algebra.TensorProduct.map φ (AlgHom.id B L) (ptF F a b i)) = ptF F (fun j => φ (a j)) b := by
  funext i
  exact map_adicEval_wpt φ ha hb _

theorem map_adicEval_ptF (F : MvFormalGroup 2 B) {S S' L : Type} [CommRing S] [Algebra B S]
    [CommRing S'] [Algebra B S'] [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) (G : MvPowerSeries (Fin 2) B) :
    Algebra.TensorProduct.map φ (AlgHom.id B L) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (ptF F a b) G) =
      MvFormalGroup.adicEval (⊥ : Ideal (S' ⊗[B] L)) (ptF F (fun j => φ (a j)) b) G := by
  rw [MvFormalGroup.map_adicEval (⊥ : Ideal (S ⊗[B] L)) (⊥ : Ideal (S' ⊗[B] L))
      (Algebra.TensorProduct.map φ (AlgHom.id B L)) Submodule.fg_bot
      (fun s hs => by rw [Ideal.mem_bot] at hs; simp [hs]) (ptF_nil F ha hb), map_ptF F φ ha hb]

end Calculus

section Generic

variable {B : Type} [CommRing B] {L : Type} [CommRing L] [Bialgebra B L]
  {S : Type} [CommRing S] [Algebra B S]

theorem cocycle_of_coboundary (δ : S →ₐ[B] S ⊗[B] L)
    (hco : ∀ s, (_root_.TensorProduct.assoc B S L L) (Algebra.TensorProduct.map δ (AlgHom.id B L) (δ s)) =
      Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L) (δ s))
    (y : S) :
    Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L) (δ y - y ⊗ₜ[B] (1 : L)) =
      (_root_.TensorProduct.assoc B S L L) (Algebra.TensorProduct.map δ (AlgHom.id B L) (δ y - y ⊗ₜ[B] (1 : L))) +
      (_root_.TensorProduct.assoc B S L L) ((δ y - y ⊗ₜ[B] (1 : L)) ⊗ₜ[B] (1 : L)) := by
  rw [map_sub, map_sub, TensorProduct.sub_tmul, map_sub, map_sub, ← hco y, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def,
    TensorProduct.assoc_tmul]
  abel

theorem sub_invariant (δ : S →ₐ[B] S ⊗[B] L) (y m : S)
    (h : δ y - y ⊗ₜ[B] (1 : L) = δ m - m ⊗ₜ[B] (1 : L)) :
    δ (y - m) = (y - m) ⊗ₜ[B] (1 : L) := by
  rw [map_sub, TensorProduct.sub_tmul]
  linear_combination h

theorem tmul_mem_map (M : Ideal S) {m : S} (hm : m ∈ M) (l : L) :
    m ⊗ₜ[B] l ∈ M.map (algebraMap S (S ⊗[B] L)) := by
  have : m ⊗ₜ[B] l = ((1 : S) ⊗ₜ[B] l) * algebraMap S (S ⊗[B] L) m := by
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, Algebra.TensorProduct.tmul_mul_tmul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hm)

theorem mem_map_of_mem_span_tmul_one (M : Ideal S) {x : S ⊗[B] L}
    (hx : x ∈ Ideal.span ((fun s : S => s ⊗ₜ[B] (1 : L)) '' (M : Set S))) :
    x ∈ M.map (algebraMap S (S ⊗[B] L)) := by
  rw [Ideal.map]
  convert hx using 2
  rfl

theorem map_id_eq_rTensor {S' : Type} [CommRing S'] [Algebra B S'] (φ : S →ₐ[B] S') (z : S ⊗[B] L) :
    Algebra.TensorProduct.map φ (AlgHom.id B L) z = φ.toLinearMap.rTensor L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s l => simp

end Generic

theorem assoc_sub {R : Type} [CommRing R] {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (u v : (M ⊗[R] N) ⊗[R] P) :
    _root_.TensorProduct.assoc R M N P (u - v) =
      _root_.TensorProduct.assoc R M N P u - _root_.TensorProduct.assoc R M N P v :=
  map_sub _ u v

end LiftStep

open LiftStep in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    [Module.Free B L] [Module.Finite B L]
    (N : ℕ) (hN : N ≠ 0)
    (δ : (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L)
    (hδ : ∀ G, δ (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ N)) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (δ' : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L)
    (hδ' : ∀ G, δ' (Ideal.Quotient.mk (I ^ (N + 1)) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ (N + 1)) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1))) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (f : MvPowerSeries (Fin 2) B) (hf : f ∈ I)
    (hinv : δ (Ideal.Quotient.mk (I ^ N) f) = Ideal.Quotient.mk (I ^ N) f ⊗ₜ[B] (1 : L)) :
    ∃ s : MvPowerSeries (Fin 2) B, s ∈ I ^ N ∧
      δ' (Ideal.Quotient.mk (I ^ (N + 1)) (f - s)) = Ideal.Quotient.mk (I ^ (N + 1)) (f - s) ⊗ₜ[B] (1 : L) := by
  classical

  obtain ⟨δ₁, hδ₁, hco₁, hcu₁, hcont₁, hq₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_levelCoaction_of_subgroup_ideal_of_ne_zero p X I hnil hmul π hπ hker
      hπnil hev hcomul hcounit (N + 1) (Nat.succ_ne_zero N)
  have hδ'eq : δ' = δ₁ := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro G
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hδ', hδ₁]
  have hco' := hco₁
  have hcu' := hcu₁
  rw [← hδ'eq] at hco' hcu'

  obtain ⟨q, hq⟩ := hnil
  have hanil : ∀ j, IsNilpotent (Ideal.Quotient.mk (I ^ (N + 1)) (MvPowerSeries.X j : MvPowerSeries (Fin 2) B)) :=
    fun j => ⟨q * (N + 1), by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_mul]
      exact Ideal.pow_mem_pow (hq j) _⟩

  let q' : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) →ₐ[B] L :=
    Ideal.Quotient.liftₐ (I ^ (N + 1)) π (fun a ha => by
      rw [← RingHom.mem_ker, hker]; exact Ideal.pow_le_self (Nat.succ_ne_zero N) ha)
  have hq'mk : ∀ G, q' (Ideal.Quotient.mk (I ^ (N + 1)) G) = π G := fun G => rfl
  have hq'surj : Function.Surjective q' := by
    intro l
    obtain ⟨G, hG⟩ := hπ l
    exact ⟨Ideal.Quotient.mk (I ^ (N + 1)) G, by rw [hq'mk, hG]⟩
  have hqδ' : ∀ s, Algebra.TensorProduct.map q' (AlgHom.id B L) (δ' s) = Coalgebra.comul (R := B) (q' s) := by
    intro s
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hδ'eq, hq'mk]
    exact hq₁ G

  let M : Ideal (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) := (I ^ N).map (Ideal.Quotient.mk (I ^ (N + 1)))
  have hkerq' : RingHom.ker q' ≤ I.map (Ideal.Quotient.mk (I ^ (N + 1))) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker] at hx
    change q' (Ideal.Quotient.mk (I ^ (N + 1)) a) = 0 at hx
    rw [hq'mk, ← RingHom.mem_ker, hker] at hx
    exact Ideal.mem_map_of_mem _ hx
  have hM : RingHom.ker q' * M = ⊥ := by
    rw [← le_bot_iff]
    calc RingHom.ker q' * M ≤ I.map (Ideal.Quotient.mk (I ^ (N + 1))) * M := Ideal.mul_mono_left hkerq'
      _ = (I * I ^ N).map (Ideal.Quotient.mk (I ^ (N + 1))) := by rw [Ideal.map_mul]
      _ = ⊥ := by rw [← pow_succ', Ideal.map_quotient_self]

  set y := Ideal.Quotient.mk (I ^ (N + 1)) f with hy
  set e := δ' y - y ⊗ₜ[B] (1 : L) with he_def

  have hle : I ^ (N + 1) ≤ I ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
  let pr : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) :=
    Ideal.Quotient.factorₐ B hle
  have hprmk : ∀ G, pr (Ideal.Quotient.mk (I ^ (N + 1)) G) = Ideal.Quotient.mk (I ^ N) G := fun G => rfl
  have hcompat : ∀ G, Algebra.TensorProduct.map pr (AlgHom.id B L) (δ' (Ideal.Quotient.mk (I ^ (N + 1)) G)) =
      δ (Ideal.Quotient.mk (I ^ N) G) := by
    intro G
    rw [hδ', hδ]
    exact map_adicEval_ptF X.F pr hanil hπnil G
  have hpre : Algebra.TensorProduct.map pr (AlgHom.id B L) e = 0 := by
    rw [he_def, map_sub, hy, hcompat, hinv, Algebra.TensorProduct.map_tmul]
    simp [hprmk]

  have hexact : Function.Exact ((M.restrictScalars B).subtype) (pr.toLinearMap) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have : Ideal.Quotient.mk (I ^ N) a = 0 := hx
      rw [Ideal.Quotient.eq_zero_iff_mem] at this
      exact ⟨⟨_, Ideal.mem_map_of_mem _ this⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
      show pr (Ideal.Quotient.mk (I ^ (N + 1)) a) = 0
      rw [hprmk, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  have hsurj : Function.Surjective pr.toLinearMap := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (I ^ (N + 1)) a, rfl⟩
  have hex := _root_.rTensor_exact L hexact hsurj
  have hmap : ∀ z, Algebra.TensorProduct.map pr (AlgHom.id B L) z = pr.toLinearMap.rTensor L z :=
    map_id_eq_rTensor pr
  have hker0 : pr.toLinearMap.rTensor L e = 0 := by rw [← hmap, hpre]
  obtain ⟨z, hz⟩ := (hex e).1 hker0

  have hcoc := cocycle_of_coboundary δ' hco' y
  rw [← he_def] at hcoc

  have key := HopfAlgebra.exists_eq_coaction_sub_tmul_one_of_cocycle δ' hco' hcu' q' hq'surj hqδ' M hM
  obtain ⟨m, hmM, hme⟩ := key
    (by
      intro m hm
      obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm
      rw [hδ'eq]
      exact mem_map_of_mem_span_tmul_one M (hcont₁ N g hg))
    e
    (by
      rw [← hz]
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb
      | tmul m l =>
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
        exact tmul_mem_map M m.2 l)
    hcoc
  obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmM
  refine ⟨s, hs, ?_⟩
  rw [map_sub]
  exact sub_invariant δ' y _ (he_def ▸ hme)

end S_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ (solution)
