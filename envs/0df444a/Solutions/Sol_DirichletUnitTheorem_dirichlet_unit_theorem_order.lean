-- Prove2me | solution 1 for DirichletUnitTheorem.dirichlet_unit_theorem_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:31:06.712567+00:00
-- url     : https://prove2.me/submissions/d98248e9-c049-4907-adc9-d355efce5592

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K]
    (O : Subring (𝓞 K)) (hO : O.toAddSubgroup.FiniteIndex) :
    Group.FG Oˣ ∧
      Module.rank ℤ (Additive Oˣ) =
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : Cardinal) := by
  classical
  let ι : Oˣ →* (𝓞 K)ˣ := Units.map O.subtype.toMonoidHom
  have hι : Function.Injective ι := fun a b h =>
    Units.ext (Subtype.ext (congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) h))
  set m := O.toAddSubgroup.index with hm_def
  have hm : m ≠ 0 := hO.index_ne_zero
  let I : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}
  have hI : I ≠ ⊥ := by
    simp only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hm
  have : Finite (𝓞 K ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let red : (𝓞 K)ˣ →* (𝓞 K ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom
  have hmem : ∀ x : 𝓞 K, x - 1 ∈ I → x ∈ O := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    have hma : m • a ∈ O.toAddSubgroup := O.toAddSubgroup.nsmul_index_mem a
    have hx' : x = 1 + m • a := by rw [nsmul_eq_mul, mul_comm, ha]; ring
    rw [hx']
    exact O.add_mem O.one_mem hma
  have hker_mem : ∀ u : (𝓞 K)ˣ, u ∈ red.ker → (u : 𝓞 K) - 1 ∈ I := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have := congrArg (fun v : (𝓞 K ⧸ I)ˣ => (v : 𝓞 K ⧸ I)) hu
    simp only [red, Units.coe_map, Units.val_one] at this
    rw [← Ideal.Quotient.eq, map_one]
    exact this
  have hker : red.ker ≤ ι.range := by
    intro u hu
    have h1 := hker_mem u hu
    have h2 := hker_mem u⁻¹ (inv_mem hu)
    refine ⟨⟨⟨u, hmem _ h1⟩, ⟨(u⁻¹ : (𝓞 K)ˣ), hmem _ h2⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩
  have hfin : ι.range.FiniteIndex := Subgroup.finiteIndex_of_le hker
  -- additive version
  let ιa : Additive Oˣ →ₗ[ℤ] Additive (𝓞 K)ˣ := (MonoidHom.toAdditive ι).toIntLinearMap
  have hιa : Function.Injective ιa := hι
  have hFin : Module.Finite ℤ (Additive Oˣ) := Module.Finite.of_injective ιa hιa
  refine ⟨GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp hFin), ?_⟩
  let S : Submodule ℤ (Additive (𝓞 K)ˣ) := LinearMap.range ιa
  have hS : Module.rank ℤ S = Module.rank ℤ (Additive Oˣ) :=
    (LinearEquiv.ofInjective ιa hιa).rank_eq.symm
  have hQ : Module.rank ℤ (Additive (𝓞 K)ˣ ⧸ S) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S x
    refine ⟨(ι.range.index : ℤ), by exact_mod_cast hfin.index_ne_zero, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, natCast_zsmul]
    obtain ⟨w, hw⟩ := ι.range.pow_index_mem y.toMul
    exact ⟨Additive.ofMul w, hw⟩
  have key := rank_quotient_add_rank_of_isDomain S
  rw [hQ, zero_add, hS] at key
  rw [key, ← Module.finrank_eq_rank, Units.finrank_eq, Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
