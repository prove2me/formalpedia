-- Prove2me | solution 1 for BddExp3SUM.profile_count
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:14:59.301247+00:00
-- url     : https://prove2.me/submissions/dbc12027-3fda-4162-90fa-9bced53bb005

import Definitions.Def_BddExp3SUM_Profiles


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BddExp3SUM
namespace ProfileProof

theorem cosetCount_le {M r : ℕ} (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) :
    cosetCount S d x ≤ S.card := by
  classical
  exact Finset.card_filter_le _ _

theorem profile_bound {M r n : ℕ} (S : Finset (Grp M r)) (hS : S.card ≤ n) :
    profileCount S ≤ (1+Nat.log 2 n)^Lcard M := by
  classical
  let tag : Grp M r → (Dvs M → Fin (Nat.log 2 n+1)) := fun x d =>
    ⟨Nat.log 2 (cosetCount S d.val x),by
      have h := Nat.log_mono_right (b:=2) (le_trans (cosetCount_le S d.val x) hS)
      omega⟩
  let repr : (Dvs M → Fin (Nat.log 2 n+1)) → (Dvs M → ℕ) :=
    fun t d => 2^(t d).val
  have he : S.image (profile S)=(S.image tag).image repr := by
    rw [Finset.image_image]
    rfl
  calc
    profileCount S=(S.image tag |>.image repr).card := congrArg Finset.card he
    _ ≤ (S.image tag).card := Finset.card_image_le
    _ ≤ Fintype.card (Dvs M → Fin (Nat.log 2 n+1)) := Finset.card_le_univ _
    _ = (1+Nat.log 2 n)^Lcard M := by simp [Lcard,Nat.add_comm]

theorem profile_partition {M r : ℕ} (S : Fin 3 → Finset (Grp M r))
    (x : Fin 3 → Grp M r) (hx : ∀ i,x i∈S i) :
    ∃! U : Fin 3 → Finset (Grp M r),IsProfileTriple S U ∧ ∀ i,x i∈U i := by
  classical
  let U : Fin 3 → Finset (Grp M r) :=
    fun i => (S i).filter fun y => profile (S i) y=profile (S i) (x i)
  refine ⟨U,⟨?_,?_⟩,?_⟩
  · intro i
    exact ⟨x i,hx i,rfl⟩
  · intro i
    exact Finset.mem_filter.mpr ⟨hx i,rfl⟩
  · rintro V ⟨hV,hxV⟩
    funext i
    obtain ⟨y,hy,he⟩ := hV i
    have hp : profile (S i) (x i)=profile (S i) y := by
      have hh := hxV i
      rw [he] at hh
      exact (Finset.mem_filter.mp hh).2
    rw [he]
    change (S i).filter (fun z => profile (S i) z=profile (S i) y)=
      (S i).filter (fun z => profile (S i) z=profile (S i) (x i))
    rw [hp]

theorem profile_count {M r n : ℕ} (S : Fin 3 → Finset (Grp M r)) (hS : ∀ i,(S i).card ≤ n) :
    (∀ i,profileCount (S i) ≤ (1+Nat.log 2 n)^Lcard M) ∧
    ∀ x : Fin 3 → Grp M r,(∀ i,x i∈S i) →
      ∃! U : Fin 3 → Finset (Grp M r),IsProfileTriple S U ∧ ∀ i,x i∈U i :=
  ⟨fun i => profile_bound (S i) (hS i),profile_partition S⟩

end ProfileProof
end BddExp3SUM

open BddExp3SUM

theorem solution {M r n : ℕ} (S : Fin 3 → Finset (Grp M r)) (hS : ∀ i, (S i).card ≤ n) :
    (∀ i, profileCount (S i) ≤ (1 + Nat.log 2 n) ^ Lcard M) ∧
    ∀ x : Fin 3 → Grp M r, (∀ i, x i ∈ S i) →
      ∃! U : Fin 3 → Finset (Grp M r), IsProfileTriple S U ∧ ∀ i, x i ∈ U i  := BddExp3SUM.ProfileProof.profile_count S hS
