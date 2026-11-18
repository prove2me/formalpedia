-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:06:46.98328+00:00
-- url     : https://prove2.me/submissions/a6d5c813-e2ac-4e78-a9db-5621585cc5da

import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Theorems.Thm_EdgeSublinearMWIS_Main_path_law_sampling
import Theorems.Thm_EdgeSublinearMWIS_Main_path_system_obstruction

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass

 theorem edge_card_bound {h : ℕ} (H : SimpleGraph (Fin h)) (d : ℕ) (hd : ∀ v,degree H v ≤ d) :
    Fintype.card (EdgeIndex H) ≤ d*h := by
  let f : EdgeIndex H → Σ u : Fin h,H.neighborSet u := fun e => ⟨e.val.1,⟨e.val.2,e.property.2⟩⟩
  have hinj : Function.Injective f := by
    intro e q heq
    apply Subtype.ext
    exact congrArg (fun z : Σ u : Fin h,H.neighborSet u => (z.1,z.2.val)) heq
  calc
    _ ≤ Fintype.card (Σ u : Fin h,H.neighborSet u) := Fintype.card_le_of_injective f hinj
    _ = ∑ u : Fin h,degree H u := by rw [Fintype.card_sigma]; simp only [Set.fintypeCard_eq_ncard,degree]
    _ ≤ ∑ _u : Fin h,d := Finset.sum_le_sum (fun u _ => hd u)
    _ = _ := by simp [Nat.mul_comm]

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.PathMass
set_option autoImplicit false

theorem solution (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ B : ℝ,0 < B ∧ ∀ ell : ℝ,1 ≤ ell →
      ∃ p : ℕ,1 ≤ p ∧ (p:ℝ) ≤ B*ell^(4*a-2) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ),
          C n G → (∀ v,0 ≤ x v ∧ x v ≤ 1) →
          (p:ℝ) ≤ vertexSum x Finset.univ →
          edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p →
          ¬∃ (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)),PathOutcome G x ell W f := by
  classical
  obtain ⟨D,hD,hfamily⟩ := path_system_obstruction C a K hereditary ha bound
  refine ⟨108*D^2+1,by positivity,?_⟩
  intro ell hell
  obtain ⟨h,H,hE,hh,hdeg,hobstruction⟩ := hfamily ell hell
  let Q : ℝ := 108*(h:ℝ)^2*ell^2
  let p : ℕ := max 1 ⌈Q⌉₊
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hp1 : 1 ≤ p := le_max_left _ _
  have hpR : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hQp : Q ≤ (p:ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast (le_max_right 1 ⌈Q⌉₊))
  have hpQ : (p:ℝ) ≤ Q+1 := by
    dsimp only [p]
    rw [Nat.cast_max]
    exact max_le (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ Q+1 by linarith)) (Nat.ceil_lt_add_one hQ0).le
  have hhex : (h:ℝ)^2 ≤ (D*ell^(2*a-2))^2 := pow_le_pow_left₀ (Nat.cast_nonneg h) hh 2
  have hexp : (2*a-2)*2+2=4*a-2 := by omega
  have hQbound : Q ≤ 108*D^2*ell^(4*a-2) := by
    calc
      _ ≤ 108*(D*ell^(2*a-2))^2*ell^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhex (by norm_num)) (sq_nonneg ell)
      _ = 108*D^2*((ell^(2*a-2))^2*ell^2) := by ring
      _ = _ := by rw [←pow_mul,←pow_add,hexp]
  have hpow : 1 ≤ ell^(4*a-2) := one_le_pow₀ hell
  have hpBound : (p:ℝ) ≤ (108*D^2+1)*ell^(4*a-2) := by nlinarith
  refine ⟨p,hp1,hpBound,?_⟩
  intro n G x hC hx hcost henergy hpaths
  obtain ⟨W,f,hf⟩ := hpaths
  have hcard : (Fintype.card (EdgeIndex H):ℝ) ≤ 3*(h:ℝ) := by exact_mod_cast edge_card_bound H 3 hdeg
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg (Fintype.card (EdgeIndex H))) hcard 2
  have hbudget : 12*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 ≤ (p:ℝ) := by
    calc
      _ ≤ 12*(3*(h:ℝ))^2*ell^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (sq_nonneg ell)
      _ = Q := by dsimp [Q]; ring
      _ ≤ _ := hQp
  obtain ⟨E,hind,hvertices,hpathvertices,hlength⟩ := path_law_sampling H G x ell W f hf hell hx
    (p:ℝ) hpR hcost henergy hbudget hE
  have hlong := hobstruction n G hC E hind
  linarith
end
